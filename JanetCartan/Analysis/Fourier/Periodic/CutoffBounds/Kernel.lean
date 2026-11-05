module

public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Passing from periodic kernel bounds to derivative norms

This is the integration and supremum step in the proof of `main:lem:smoothing`.
The derivative kernel representations and their L¹ estimates are explicit inputs.
In particular this file does not assert their existence for a Fourier cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `main:lem:smoothing`: an operator-valued periodic kernel acts on bounded
    fields with norm at most its L¹ operator norm times the field bound. -/
theorem norm_periodicKernel_integral_le
    (K : Torus n → F →L[ℝ] G) (f : Torus n → F) {M : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ M) (hK : Integrable (fun y ↦ ‖K y‖)) :
    ‖∫ y, K y (f y)‖ ≤ (∫ y, ‖K y‖) * M := by
  calc
    _ ≤ ∫ y, ‖K y‖ * M := norm_integral_le_of_norm_le
      (hK.mul_const M) (Filter.Eventually.of_forall (fun y ↦
        (K y).le_opNorm (f y) |>.trans
          (mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _))))
    _ = _ := integral_mul_const M _

private theorem cNorm_le_sum_of_scaled_derivative_bounds
    {s : Set E} (hs : s.Nonempty) (g : E → F) (r : ℕ)
    {R M : ℝ} (hR : 1 ≤ R) (hM : 0 ≤ M) (C : ℕ → ℝ)
    (hC : ∀ j ≤ r, 0 ≤ C j)
    (hderiv : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g x‖ ≤ C j * R ^ j * M) :
    cNorm s r g ≤ (∑ j ∈ Finset.range (r + 1), C j) * R ^ r * M := by
  unfold cNorm
  calc
    _ ≤ ∑ j ∈ Finset.range (r + 1), C j * R ^ r * M := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      apply csSup_le (hs.image _)
      rintro _ ⟨x, hx, rfl⟩
      exact (hderiv j hjr x hx).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hjr) (hC j hjr)) hM)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- `main:eq:smoothing-low`: derivative kernel representations with L¹ bounds
    `C j * R ^ j` imply the C^r bound for `R ≥ 1`. This is conditional on the
    representations and kernel estimates, which must be proved for the fixed cutoff. -/
theorem cNorm_le_of_periodic_derivative_kernels
    {s : Set E} (hs : s.Nonempty) (g : E → F) (f : Torus n → G) (r : ℕ)
    (K : (j : ℕ) → E → Torus n → G →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)
    {R M : ℝ} (hR : 1 ≤ R) (hM : 0 ≤ M) (C : ℕ → ℝ)
    (hC : ∀ j ≤ r, 0 ≤ C j) (hf : ∀ y, ‖f y‖ ≤ M)
    (hK : ∀ j ≤ r, ∀ x ∈ s, Integrable (fun y ↦ ‖K j x y‖))
    (hmass : ∀ j ≤ r, ∀ x ∈ s, (∫ y, ‖K j x y‖) ≤ C j * R ^ j)
    (hrep : ∀ j ≤ r, ∀ x ∈ s, iteratedFDeriv ℝ j g x = ∫ y, K j x y (f y)) :
    cNorm s r g ≤ (∑ j ∈ Finset.range (r + 1), C j) * R ^ r * M := by
  apply cNorm_le_sum_of_scaled_derivative_bounds hs g r hR hM C hC
  intro j hj x hx
  rw [hrep j hj x hx]
  exact (norm_periodicKernel_integral_le (K j x) f hf (hK j hj x hx)).trans
    (mul_le_mul_of_nonneg_right (hmass j hj x hx) hM)

/-- `main:eq:smoothing-high`: a kernel representation of an error with L¹ mass
    at most `A` gives a C⁰ bound. For a tail estimate the input field is a derivative
    field and `A = C_N * R⁻ᴺ`; constructing that representation is a separate step. -/
theorem cNorm_zero_le_of_periodic_kernel
    {s : Set E} (hs : s.Nonempty) (g : E → F) (f : Torus n → G)
    (K : E → Torus n → G →L[ℝ] F) {A M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ y, ‖f y‖ ≤ M)
    (hK : ∀ x ∈ s, Integrable (fun y ↦ ‖K x y‖))
    (hmass : ∀ x ∈ s, (∫ y, ‖K x y‖) ≤ A)
    (hrep : ∀ x ∈ s, g x = ∫ y, K x y (f y)) :
    cNorm s 0 g ≤ A * M := by
  simp only [cNorm, zero_add, Finset.sum_range_one, norm_iteratedFDeriv_zero]
  apply csSup_le (hs.image _)
  rintro _ ⟨x, hx, rfl⟩
  change ‖g x‖ ≤ A * M
  rw [hrep x hx]
  exact (norm_periodicKernel_integral_le (K x) f hf (hK x hx)).trans
    (mul_le_mul_of_nonneg_right (hmass x hx) hM)

end JanetCartan
