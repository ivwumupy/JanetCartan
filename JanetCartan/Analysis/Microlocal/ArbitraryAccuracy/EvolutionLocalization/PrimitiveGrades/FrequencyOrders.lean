module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers

/-!
# Real symbol orders on the physical graph branches

The multiplier cone compares the spatial and spacetime brackets. The bounded
branches retain `max 1 (branchRadius low j)`, and negative orders use the lower
comparison, rather than an order-zero estimate. Consumer: the physical base
amplitude grade in `exists_graph_factor_sobolev_bound_of_primitive_grades`.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Noncomparable
variable {d : ℕ}

/-- One fixed comparison constant works for any real order. The second term
is essential when the symbol order is negative (`app:ch_regular:eq:high-amplitude`). -/
def elapsedOrderConstant (C s : ℝ) : ℝ :=
  max ((5 : ℝ) ^ s) ((2 * (C + 1))⁻¹ ^ s)

/-- Nonnegativity of the real-order branch constant
(`app:ch_regular:eq:high-amplitude`). -/
theorem elapsedOrderConstant_nonneg (C s : ℝ) : 0 ≤ elapsedOrderConstant C s :=
  (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) s).trans (le_max_left _ _)

/-- Spatial symbol weights transfer to the actual graph branch weight,
including every bounded branch and every negative real order. Only the
original multiplier cone and the physical annulus endpoints are used. -/
theorem spatialBracket_rpow_le_branchRadius
    {C : ℝ} (hC : 0 ≤ C) (s : ℝ) (low : Bool) (j : ℕ)
    (ξ : Euclidean (d + 1)) (hcone : |ξ 0| ≤ C * ‖spatialPart ξ‖)
    (hξ : graphLower low j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ graphUpper low j) :
    (1 + ‖spatialPart ξ‖) ^ s ≤
      (max 1 (branchRadius low j)) ^ s * elapsedOrderConstant C s := by
  let R := max 1 (branchRadius low j)
  let w := 1 + ‖spatialPart ξ‖
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hw : 0 < w := by dsimp [w]; positivity
  have hC0 : 0 < 2 * (C + 1) := by positivity
  have hu : w ≤ 5 * R := by
    have hr : branchRadius low j ≤ R := le_max_right _ _
    have ht := (graphLower_bounds low j).2
    have hn := norm_spatialPart_le ξ
    dsimp [w, graphUpper] at *
    linarith [hξ.2]
  have hl' : R ≤ 2 * (C + 1) * w := by
    apply max_le
    · dsimp [w]
      nlinarith [norm_nonneg (spatialPart ξ)]
    · have hg := (graphLower_bounds low j).1.trans hξ.1
      have hc := norm_le_spatial_of_cone hcone
      dsimp [w]
      nlinarith
  have hl : (2 * (C + 1))⁻¹ * R ≤ w := by
    rw [inv_mul_eq_div, div_le_iff₀ hC0]
    simpa only [mul_comm] using hl'
  rcases le_total 0 s with hs | hs
  · calc
      w ^ s ≤ (5 * R) ^ s := Real.rpow_le_rpow hw.le hu hs
      _ = R ^ s * (5 : ℝ) ^ s := by
        rw [Real.mul_rpow (by norm_num) hR0.le, mul_comm]
      _ ≤ R ^ s * elapsedOrderConstant C s :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg hR0.le s)
  · calc
      w ^ s ≤ ((2 * (C + 1))⁻¹ * R) ^ s :=
        Real.rpow_le_rpow_of_nonpos (mul_pos (inv_pos.mpr hC0) hR0) hl hs
      _ = R ^ s * ((2 * (C + 1))⁻¹ ^ s) := by
        rw [Real.mul_rpow (inv_nonneg.mpr hC0.le) hR0.le, mul_comm]
      _ ≤ R ^ s * elapsedOrderConstant C s :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg hR0.le s)

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades
