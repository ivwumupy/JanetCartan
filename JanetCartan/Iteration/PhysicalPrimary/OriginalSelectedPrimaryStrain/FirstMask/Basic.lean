module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask

/-! # The common price of both actual primary derivative factors

The coefficient Jacobian and complete raw amplitude have their independently
proved profiles. Their sum is one fixed price usable by the first mask and
negative moments for either original quadrature (`main:eq:primary-strain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

/-- The full raw amplitude may be rotated without changing its profile;
the sum of the two original costs bounds both factors at the same R. -/
theorem common_quadrature_profile {n N : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U)
    (A D : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (CA CD : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hCA : ∀ q, 0 ≤ CA q) (hCD : ∀ q, 0 ≤ CD q)
    (hA : ∀ y ∈ U, ∀ q, ‖iteratedFDeriv ℝ q A y‖ ≤ CA q * R^q)
    (hD : ContDiffOn ℝ ∞ D U)
    (hDj : ∀ q y, y ∈ U → ‖iteratedFDeriv ℝ q D y‖ ≤ CD q * R^q)
    (imaginary : Bool) :
    ContDiffOn ℝ ∞ (quadratureScalar imaginary • D) U ∧
      ∀ y ∈ U, ∀ q,
        ‖iteratedFDeriv ℝ q A y‖ ≤ (CA q + CD q) * R^q ∧
        ‖iteratedFDeriv ℝ q (quadratureScalar imaginary • D) y‖ ≤ (CA q + CD q) * R^q := by
  obtain ⟨hs,hj⟩ := quadrature_profile hU D CD R hD hDj imaginary
  refine ⟨hs,fun y hy q ↦ ⟨?_,?_⟩⟩
  · exact (hA y hy q).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hCD q)) (pow_nonneg hR q))
  · exact (hj q y hy).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hCA q)) (pow_nonneg hR q))

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
end
