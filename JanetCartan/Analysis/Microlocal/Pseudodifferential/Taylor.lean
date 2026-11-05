module

public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Finite Taylor integrals for full amplitudes

The Taylor step in `app:ch_regular_base:eq:actual-pdo-remainder`, before frequency
integration by parts. The codomain can be a space of matrices with its chosen norm.
All derivatives are genuine Fréchet derivatives. The estimates below use precisely
one extra derivative, independently of the finite Taylor order.
-/

@[expose] public noncomputable section

open scoped ContDiff
open MeasureTheory

namespace JanetCartan.Pseudodifferential

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the finite Taylor polynomial
at the diagonal, evaluated on the source displacement. -/
def amplitudeTaylorPolynomial (f : E → F) (n : ℕ) (x h : E) : F :=
  ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ k f x (fun _ ↦ h)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the exact integral remainder;
the source segment is retained inside the amplitude. -/
def amplitudeTaylorRemainder (f : E → F) (n : ℕ) (x h : E) : F :=
  (n.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
    (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • h) (fun _ ↦ h)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact finite Taylor expansion
on a source segment. Only smoothness on that segment is required. -/
theorem amplitude_eq_taylorPolynomial_add_remainder [CompleteSpace F]
    (f : E → F) (n : ℕ) (x h : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (x + t • h)) :
    f (x + h) = amplitudeTaylorPolynomial f n x h + amplitudeTaylorRemainder f n x h :=
  map_add_eq_sum_add_integral_iteratedFDeriv hf

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the first-order source Taylor
identity with the full Fréchet derivative inside the integral. -/
theorem amplitude_eq_diagonal_add_integral [CompleteSpace F] (f : E → F) (x y : E)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f (x + t • (y - x))) :
    f y = f x + ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x)) (y - x) := by
  simpa [amplitudeTaylorPolynomial, amplitudeTaylorRemainder] using
    amplitude_eq_taylorPolynomial_add_remainder f 0 x (y - x) hf

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the linear Taylor coefficient
with the actual source cutoff retained inside the coefficient. -/
def sourceTaylorCoefficient (f : E → F) (β : E → ℝ) (x y : E) : E →L[ℝ] F :=
  β y • ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x))

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the full amplitude splits
exactly into its cut-off diagonal and its linear source Taylor coefficient. -/
theorem amplitude_eq_diagonal_add_sourceTaylorCoefficient [CompleteSpace F]
    (f : E → F) (β : E → ℝ) (x y : E) (hf : ContDiff ℝ 1 f)
    (hβ : ∀ z ∈ Function.support f, β z = 1) :
    f y = β y • f x + sourceTaylorCoefficient f β x y (y - x) := by
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.continuous_fderiv (by simp)).comp (by fun_prop)
  have hmask : β y • f y = f y := by
    by_cases hy : f y = 0
    · simp [hy]
    · rw [hβ y hy, one_smul]
  calc
    f y = β y • f y := hmask.symm
    _ = β y • (f x + ∫ t in (0 : ℝ)..1,
        fderiv ℝ f (x + t • (y - x)) (y - x)) := by
      rw [amplitude_eq_diagonal_add_integral f x y (fun _ _ ↦ hf.contDiffAt)]
    _ = _ := by
      rw [smul_add, sourceTaylorCoefficient, smul_apply,
        ContinuousLinearMap.intervalIntegral_apply hint]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a finite remainder bound with
the explicit derivative shift `n ↦ n + 1`. This is a bound on the Taylor integral,
not yet the symbol estimate after frequency integration by parts. -/
theorem norm_amplitudeTaylorRemainder_le (f : E → F) (n : ℕ) (x h : E) {M : ℝ}
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • h)‖ ≤ M) :
    ‖amplitudeTaylorRemainder f n x h‖ ≤
      (n.factorial : ℝ)⁻¹ * (M * ‖h‖ ^ (n + 1)) := by
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • h) (fun _ ↦ h)‖ ≤
      M * ‖h‖ ^ (n + 1) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := M * ‖h‖ ^ (n + 1)) ?_).trans_eq (by simp)
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      have ht'' : 0 < t ∧ t ≤ 1 := by simpa using ht
      exact ⟨ht''.1.le, ht''.2⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht'.2
    have ht1 : 1 - t ≤ 1 := sub_le_self _ ht'.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 n)]
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) f (x + t • h) (fun _ ↦ h)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1) (norm_nonneg _)
      _ ≤ M * ‖h‖ ^ (n + 1) := by
        rw [one_mul]
        calc
          _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • h)‖ * ‖h‖ ^ (n + 1) := by
            simpa using (iteratedFDeriv ℝ (n + 1) f (x + t • h)).le_opNorm (fun _ ↦ h)
          _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ht') (pow_nonneg (norm_nonneg _) _)
  rw [amplitudeTaylorRemainder, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (Nat.cast_nonneg _))

end JanetCartan.Pseudodifferential
