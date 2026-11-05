module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData

/-!
# Coefficient jets on the original primary source chart

The consumers are `PhysicalPairs.SampledMask.first_mask.hQj/hAj` and the
negative source moments in `main:eq:primary-strain` of paper-v2. The full
operator profile and the twice-Jacobian profile retain their original prices;
only the slow coefficient scale is increased to the history scale.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles

/-- The full stress coefficient's compact profile gives ordinary jets on the
entire source chart, with the same fixed price (`app:ch_regular:eq:source-tail`). -/
theorem stress_jets_on_chart {n : ℕ}
    {Q : Euclidean n → Fin n → MetricTensor n} {U S : Set (Euclidean n)}
    (hS : IsCompact S) (hUS : U ⊆ S) (hQ : ContDiff ℝ ∞ Q)
    {reserve : ℕ} {T R : ℝ} {C : ℕ → ℝ}
    (hT : 1 ≤ T) (hTR : T ≤ R) (hC : ∀ q, 0 ≤ C q)
    (hj : HasDerivativeProfile S Q reserve T C) :
    ∀ y ∈ U, ∀ q, ‖iteratedFDeriv ℝ q Q y‖ ≤ C q * R ^ q := by
  intro y hy q
  apply (norm_iteratedFDeriv_le_cNorm hS (hQ.of_le (by simp)) (hUS hy) le_rfl).trans
  apply (hj q).trans
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_right₀ hT (Nat.sub_le q reserve)).trans
      (pow_le_pow_left₀ (zero_le_one.trans hT) hTR q)) (hC q)

/-- Promote the actual matrix coefficient's jets from `T` to `R`, without
changing its prehistory price (`main:eq:primary-strain`). -/
theorem matrix_coefficient_jets_mono {n N : ℕ}
    {A : Euclidean n → Matrix (Fin N) (Fin n) ℂ} {U : Set (Euclidean n)}
    {T R : ℝ} {C : ℕ → ℝ} (hT : 0 ≤ T) (hTR : T ≤ R)
    (hC : ∀ q, 0 ≤ C q)
    (hj : ∀ y ∈ U, ∀ q, ‖iteratedFDeriv ℝ q A y‖ ≤ C q * T ^ q) :
    ∀ y ∈ U, ∀ q, ‖iteratedFDeriv ℝ q A y‖ ≤ C q * R ^ q := by
  intro y hy q
  exact (hj y hy q).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTR q) (hC q))

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles
end
