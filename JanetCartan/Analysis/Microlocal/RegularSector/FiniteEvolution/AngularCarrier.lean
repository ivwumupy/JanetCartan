module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.RetardedRadii
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution

/-!
# The selected finite angular masks fit the retained retarded cones

The source-radius comparison retained by `exists_actualMaskFamily_with_retarded_radii`
puts the original angular neighborhoods inside the smaller `UniformEvolution`
cone. Compactness of each unit carrier supplies its temporal aperture. Neither
the selected cover nor its masks are shrunk.

Consumer: `exists_retained_local_solver_and_residual` on the same selected chart,
for `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteEvolution
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicPhase Characteristic.EvolutionIntegral
open FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

/-- The actual source mask is small enough for the retained graph's inner
angular margin. The inequalities come from the strengthened constructor,
before varying coefficients (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem neighborhoodRadius_le_retained_quarter (c : LocalChart Ω x RQ A₀ ξ M)
    (hρb : c.bufferRadius ≤ c.targetRadius)
    (hsrcρ : c.maskRadius ≤ c.bufferRadius / 4) :
    c.neighborhoodRadius ≤ retainedRadius c.targetRadius c.bufferRadius / 4 := by
  have hr : c.neighborhoodRadius ≤ c.maskRadius / 8 := min_le_left _ _
  rw [retainedRadius, min_eq_right hρb]
  have := c.bufferRadius_pos
  linarith

/-- Every selected unit carrier has a fixed temporal aperture in the SAME
retained section. This discharges the `hcarrier` input of the actual retarded
constructor; no temporal cone hypothesis is added to the finite family.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_chart_temporal_aperture (c : LocalChart Ω x RQ A₀ ξ M)
    (hρb : c.bufferRadius ≤ c.targetRadius)
    (hsrcρ : c.maskRadius ≤ c.bufferRadius / 4)
    (mask : E → ℝ) (hsupport : tsupport mask ⊆ c.angularNeighborhood) :
    ∃ aperture > (0 : ℝ),
      tsupport (mask ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1 ⊆
        fullAngularCone c.radialSection (coordinateSplit c.index ξ).2
          (retainedRadius c.targetRadius c.bufferRadius / 4) (aperture / 2) := by
  let K := tsupport (mask ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1
  have hcone {ζ : E} (hζ : ζ ∈ K) : spatialPart ζ ∈ c.spatialCone := by
    have hp := hsupport (tsupport_comp_subset_preimage mask
      (physicalCoordinates c.index).continuous hζ.1)
    simpa only [LocalChart.angularNeighborhood, mem_preimage,
      split_physicalCoordinates] using hp
  have hpositive {ζ : E} (hζ : ζ ∈ K) : 0 < c.radialSection (spatialPart ζ) :=
    (hcone hζ).1
  have hK : IsCompact K := (isCompact_sphere (0 : E) 1).inter_left (isClosed_tsupport _)
  have hratio : ContinuousOn (fun ζ : E ↦ |ζ 0| / c.radialSection (spatialPart ζ)) K :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).continuous.abs.continuousOn).div
      (c.radialSection.continuous.comp spatialPartCLM.continuous).continuousOn
      (fun ζ hζ ↦ (hpositive hζ).ne')
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hratio
  refine ⟨2 * (max A 0 + 1), by positivity, ?_⟩
  intro ζ hζ
  refine ⟨⟨(hcone hζ).1, ball_subset_ball
    (neighborhoodRadius_le_retained_quarter c hρb hsrcρ) (hcone hζ).2⟩, ?_⟩
  have hbound : |ζ 0| / c.radialSection (spatialPart ζ) ≤ A :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hA ζ hζ)
  apply (div_lt_iff₀ (hpositive hζ)).mp
  have := le_max_left A 0
  linarith

end JanetCartan.RegularSector.FiniteEvolution
