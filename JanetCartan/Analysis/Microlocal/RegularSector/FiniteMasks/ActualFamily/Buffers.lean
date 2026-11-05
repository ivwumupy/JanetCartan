module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Shells

/-!
# The actual right supports stay inside the retained local buffers

These are geometric consequences of the constructed angular and physical
neighborhoods. The root, two-time phase and source mask are the same local
witnesses, with no replacement chart or section.
Consumer: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

namespace LocalChart

/-- The literal physical right multiplier remains in the actual angular
cone, including all closed-support shoulders (`retarded-kernel`). -/
theorem angularNeighborhood_of_mem_rightSupport (c : LocalChart Ω x RQ A₀ ξ M)
    {χ : E → ℝ} (hχ : tsupport χ ⊆ c.angularNeighborhood)
    {L : ℝ} (hL : 1 ≤ L) {ζ : E} (hζ : ζ ∈ tsupport (dilatedConicMask χ L)) :
    ζ ∈ c.angularNeighborhood := by
  have hs := dilatedConicMask_tsupport_subset χ (zero_lt_one.trans_le hL) hζ
  simpa only [NormedSpace.norm_smul_normalize] using
    c.smul_mem_angularNeighborhood (hχ hs.2) (zero_lt_one.trans_le (hL.trans hs.1))

/-- The normalized physical pair lies inside the SAME two-time amplitude
buffer, on which the retained local producer controls its phase and matrices.
Source: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem pair_mem_conic_buffer (c : LocalChart Ω x RQ A₀ ξ M)
    {y z ζ : E} (hy : y ∈ c.physicalNeighborhood)
    (hz : z ∈ c.physicalNeighborhood) (hζ : ζ ∈ c.angularNeighborhood) :
    ((coordinateSplit c.index y).1, ((coordinateSplit c.index z).1,
      ((coordinateSplit c.index y).2, (coordinateSplit c.index ζ).2))) ∈
    ConicPhase.domain c.radialSection
      (ball ((coordinateSplit c.index x).1, ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index ξ).2)))
          (c.bufferRadius / 2)) := by
  have hr : c.neighborhoodRadius < c.bufferRadius / 2 := by
    have hle : c.neighborhoodRadius ≤ c.bufferRadius / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have := c.bufferRadius_pos
    linarith
  have hy' : dist (coordinateSplit c.index y) (coordinateSplit c.index x) <
      c.neighborhoodRadius := hy
  have hz' : dist (coordinateSplit c.index z) (coordinateSplit c.index x) <
      c.neighborhoodRadius := hz
  rw [Prod.dist_eq, max_lt_iff] at hy' hz'
  refine ⟨hζ.1, ?_⟩
  simp only [ConicPhase.normalize, mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨hy'.1.trans hr, hz'.1.trans hr, hy'.2.trans hr, hζ.2.trans hr⟩

/-- The normalized diagonal also lies in the retained root ball, where the
original determinant and minor/transport gaps hold (`characteristic-kernel`). -/
theorem diagonal_mem_root_buffer (c : LocalChart Ω x RQ A₀ ξ M)
    {y ζ : E} (hy : y ∈ c.physicalNeighborhood) (hζ : ζ ∈ c.angularNeighborhood) :
    ((coordinateSplit c.index y).1, ((coordinateSplit c.index y).2,
      (c.radialSection (coordinateSplit c.index ζ).2)⁻¹ •
        (coordinateSplit c.index ζ).2)) ∈
      closedBall ((coordinateSplit c.index x).1,
        ((coordinateSplit c.index x).2, (coordinateSplit c.index ξ).2)) c.rootRadius := by
  have hr : c.neighborhoodRadius < c.rootRadius := by
    have hle : c.neighborhoodRadius ≤ c.rootRadius / 4 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have := c.rootRadius_pos
    linarith
  have hy' : dist (coordinateSplit c.index y) (coordinateSplit c.index x) <
      c.neighborhoodRadius := hy
  rw [Prod.dist_eq, max_lt_iff] at hy'
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff]
  exact ⟨(hy'.1.trans hr).le, (hy'.2.trans hr).le, (hζ.2.trans hr).le⟩

/-- The original physical support stays strictly above the same fixed lower
time as the local source mask (`retarded-kernel`). -/
theorem physical_lower_buffer (c : LocalChart Ω x RQ A₀ ξ M)
    {y : E} (hy : y ∈ c.physicalNeighborhood) :
    (coordinateSplit c.index x).1 - c.maskRadius < (coordinateSplit c.index y).1 := by
  have hy' : dist (coordinateSplit c.index y) (coordinateSplit c.index x) <
      c.neighborhoodRadius := hy
  rw [Prod.dist_eq, max_lt_iff] at hy'
  have hlt := (abs_lt.mp hy'.1).1
  have hr := c.neighborhoodRadius_lt_mask
  have := c.maskRadius_pos
  linarith

end LocalChart
end JanetCartan.RegularSector.FiniteMasks.ActualFamily
