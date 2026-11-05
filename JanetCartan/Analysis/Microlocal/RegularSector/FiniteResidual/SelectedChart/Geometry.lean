module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization

/-!
# The common output lies in the same retained chart

The smaller physical output from `PhysicalConstruction` supplies the elapsed
box, exact time slab, time plateau and coefficient-extension carrier needed by
the supported residual proof. None of these conclusions asserts containment
of the whole elapsed chart in the transported amplitude support.
Consumer: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

private theorem common_output_mem_physical_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    {y : E} (hy : y ∈ tsupport (fun z ↦ (output (physicalCoordinates (f.chart p).index z) : ℂ))) :
    physicalCoordinates (f.chart p).index y ∈ closedBall x (4 * f.physicalRadius) := by
  have hphys : physicalCoordinates (f.chart p).index y ∈ tsupport output :=
    tsupport_comp_subset Complex.ofReal_zero output
      (tsupport_comp_subset_preimage (fun z ↦ (output z : ℂ))
        (physicalCoordinates (f.chart p).index).continuous hy)
  exact closedBall_subset_closedBall (by linarith [f.physicalRadius_pos])
    (ball_subset_closedBall (hout hphys))

private theorem retained_geometry_of_support_in_chart
    {ξ : E} (c : LocalChart Ω x RQ A₀ ξ M)
    (hρb : c.bufferRadius ≤ c.targetRadius)
    (hsrcρ : c.maskRadius ≤ c.bufferRadius / 4) (χout : E → ℂ)
    (hchart : ∀ y ∈ tsupport χout, physicalCoordinates c.index y ∈ c.physicalNeighborhood) :
    let z : RootState (Euclidean d) :=
      ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index ξ).2))
    (tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius c.targetRadius c.bufferRadius / 2)) ∧
    (∀ y ∈ tsupport χout,
      y 0 ∈ Icc (z.1 - c.maskRadius / 2) (z.1 - c.maskRadius / 2 + 3 * c.maskRadius / 4)) ∧
    (∀ y ∈ tsupport χout, c.timeMask =ᶠ[𝓝 (y 0)] fun _ ↦ (1 : ℝ)) := by
  intro z
  have hdist y (hy : y ∈ tsupport χout) :
      dist (y 0) z.1 < c.neighborhoodRadius ∧
        dist (spatialPart y) z.2.1 < c.neighborhoodRadius := by
    have h := hchart y hy
    change dist (coordinateSplit c.index (physicalCoordinates c.index y))
      (coordinateSplit c.index x) < c.neighborhoodRadius at h
    rw [split_physicalCoordinates, Prod.dist_eq, max_lt_iff] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hr := neighborhoodRadius_le_retained_quarter c hρb hsrcρ
    have hpos := (retainedRadius_bounds c.targetRadius_pos c.bufferRadius_pos).1
    exact ⟨(hdist y hy).1.trans_le (by linarith),
      (hdist y hy).2.trans_le (by linarith)⟩
  · intro y hy
    have h := (hdist y hy).1
    rw [Real.dist_eq, abs_lt] at h
    have hr := c.neighborhoodRadius_lt_mask
    have hp := c.maskRadius_pos
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro y hy
    simpa only [split_physicalCoordinates] using c.timeMask_plateau_of_mem (hchart y hy)

/-- The ORIGINAL finite-family output has the exact retained box, slab and
same time plateau needed to construct the regularizations. Using this mask
keeps the four PDO budgets exactly as supplied by `FiniteAlgebraic.Construction`
and `FinitePdo.Source`; localization to the smaller common measurement is
performed afterwards (`energy-complete-residual`). -/
theorem selected_output_retained_geometry
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) :
    let c := f.chart p
    let z : RootState (Euclidean d) :=
      ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    (tsupport (FiniteAlgebraic.chartOutputMask f p) ⊆
      elapsedPhysicalBox z (retainedRadius c.targetRadius c.bufferRadius / 2)) ∧
    (∀ y ∈ tsupport (FiniteAlgebraic.chartOutputMask f p),
      y 0 ∈ Icc (z.1 - c.maskRadius / 2) (z.1 - c.maskRadius / 2 + 3 * c.maskRadius / 4)) ∧
    (∀ y ∈ tsupport (FiniteAlgebraic.chartOutputMask f p),
      c.timeMask =ᶠ[𝓝 (y 0)] fun _ ↦ (1 : ℝ)) := by
  apply retained_geometry_of_support_in_chart (f.chart p) hρb hsrcρ
  intro y hy
  apply f.physical_supports_in_chart p
  exact Or.inr (tsupport_comp_subset Complex.ofReal_zero f.outputMask
    (tsupport_comp_subset_preimage (fun z ↦ (f.outputMask z : ℂ))
      (physicalCoordinates (f.chart p).index).continuous hy))

/-- The common physical output has the precise box and lower/upper time
endpoints required by the retarded producer, and lies in the SAME time-mask
plateau. These follow from actual finite-family geometry, without blanket
elapsed-chart containment (`retarded-kernel`). -/
theorem common_output_retained_geometry
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius) :
    let c := f.chart p
    let z : RootState (Euclidean d) :=
      ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    let χout := fun y ↦ (output (physicalCoordinates c.index y) : ℂ)
    (tsupport χout ⊆ elapsedPhysicalBox z (retainedRadius c.targetRadius c.bufferRadius / 2)) ∧
    (∀ y ∈ tsupport χout,
      y 0 ∈ Icc (z.1 - c.maskRadius / 2) (z.1 - c.maskRadius / 2 + 3 * c.maskRadius / 4)) ∧
    (∀ y ∈ tsupport χout, c.timeMask =ᶠ[𝓝 (y 0)] fun _ ↦ (1 : ℝ)) := by
  apply retained_geometry_of_support_in_chart (f.chart p) hρb hsrcρ
  intro y hy
  exact f.physicalBall_in_chart p (common_output_mem_physical_ball f p output hout hy)

/-- Construct global smooth coefficient extensions near the literal common
output carrier from original coefficient smoothness and the selected family's
physical support. Both the principal coefficients and `B` are retained as
germs there; the supported residual theorem can therefore use the original
coefficients in its final tested equation (`energy-complete-residual`). -/
theorem exists_common_output_coefficient_extensions
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius) :
    ∃ Ae : E → Fin (d + 1) → Mat, ∃ Be : E → Mat,
      ContDiff ℝ ∞ Ae ∧ ContDiff ℝ ∞ Be ∧
      ∀ y ∈ tsupport (fun z ↦ (output (physicalCoordinates (f.chart p).index z) : ℂ)),
        Ae =ᶠ[𝓝 y] coefficient (f.chart p).index Q ∧
          Be =ᶠ[𝓝 y] zeroth (f.chart p).index B := by
  apply exists_smooth_coordinate_coefficients (f.chart p).index hΩ Q B hQ hB
    (isClosed_tsupport _)
  intro y hy
  exact hKΩ (f.physicalBall_coefficientDomain (common_output_mem_physical_ball f p output hout hy))

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
