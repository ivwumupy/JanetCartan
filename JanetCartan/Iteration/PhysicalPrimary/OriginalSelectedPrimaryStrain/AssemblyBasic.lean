module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalStrain

/-! # Scalar assembly of the actual primary strain estimate

The two source quadratures share one uniform discrepancy price. After the
original finite sampled sum, its ordinary carrier power gives exactly the
revised exponent in `main:eq:primary-strain`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

/-- Transfer the common source price through the actual two-quadrature
comparison, retaining the exact fixed reconstruction coefficient. -/
theorem both_quadrature_bounds {e a b S C t : ℝ} (hS : 0 ≤ S)
    (he : e ≤ S * (a+b)) (ha : a ≤ C*t) (hb : b ≤ C*t) :
    e ≤ (S * (C+C)) * t := by
  exact (he.trans (mul_le_mul_of_nonneg_left (add_le_add ha hb) hS)).trans_eq (by ring)

/-- The finite-sampling factor and undoubled carrier yield the literal v2
primary-strain power, with no change to either underlying scale. -/
theorem combine_strain_powers {R : ℝ} (hR : 0 < R)
    (C δ a b : ℝ) (q : ℕ) :
    (C*δ) * (R^a * (R^b)^(-(q:ℝ))) = (C*δ) * R^(a-b*(q:ℝ)) := by
  rw [← Real.rpow_mul hR.le,← Real.rpow_add hR]
  congr 1
  congr 1
  ring

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end
