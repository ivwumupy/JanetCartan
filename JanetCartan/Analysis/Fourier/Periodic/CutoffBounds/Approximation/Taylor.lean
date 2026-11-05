module

public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Taylor remainders with exactly the requested number of derivatives

These are the real vector-valued Taylor estimates for `main:eq:smoothing-high`.
The derivative bound on the fundamental cell controls the whole integration segment
by periodicity; no additional derivatives depending on the dimension are used.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:smoothing-high`: the Taylor polynomial of orders strictly below `N`. -/
def cutoffTaylorPolynomial (f : E → F) (N : ℕ) (x y : E) : F :=
  ∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ ↦ y)

/-- `main:eq:smoothing-high`: an order `N + 1` Taylor remainder uses only the
`N + 1` derivative bound, uniformly on segments of arbitrary length. -/
theorem norm_sub_cutoffTaylorPolynomial_le [CompleteSpace F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N : ℕ) {M : ℝ}
    (hM : ∀ z, ‖iteratedFDeriv ℝ (N + 1) f z‖ ≤ M) (x y : E) :
    ‖f (x + y) - cutoffTaylorPolynomial f (N + 1) x y‖ ≤
      (N.factorial : ℝ)⁻¹ * M * ‖y‖ ^ (N + 1) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (x := x) (y := y) (n := N) (fun t _ ↦ (hf.of_le (by simp)).contDiffAt)
  have hint : ‖∫ t in (0 : ℝ)..1,
      (1 - t) ^ N • iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y)‖ ≤
      M * ‖y‖ ^ (N + 1) := by
    have hb (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖(1 - t) ^ N • iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y)‖ ≤
          M * ‖y‖ ^ (N + 1) := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have ht1 : 1 - t ≤ 1 := by linarith [ht.1]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 _)]
      calc
        _ ≤ 1 * ‖iteratedFDeriv ℝ (N + 1) f (x + t • y) (fun _ ↦ y)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1) (norm_nonneg _)
        _ ≤ M * ‖y‖ ^ (N + 1) := by
          simp only [one_mul]
          calc
            _ ≤ ‖iteratedFDeriv ℝ (N + 1) f (x + t • y)‖ * ‖y‖ ^ (N + 1) := by
              simpa using (iteratedFDeriv ℝ (N + 1) f (x + t • y)).le_opNorm (fun _ ↦ y)
            _ ≤ _ := mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (norm_nonneg _) _)
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [hTaylor, ← cutoffTaylorPolynomial, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (N.factorial : ℝ)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hint (by positivity)).trans_eq (by ring)

/-- `main:eq:smoothing-high`: exactly `N` cell derivatives control all lower
lifted derivatives globally. -/
theorem IsSmoothPeriodic.norm_iteratedFDeriv_le_cNorm {n : ℕ}
    {f : Torus n → F} (hf : IsSmoothPeriodic f) {N j : ℕ} (hj : j ≤ N)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
      cNorm (fundamentalCell n) N (periodicLift f) :=
  norm_iteratedFDeriv_periodicLift_le f j (fun _ hz ↦
    JanetCartan.norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n) (hf.2.of_le (by simp)) hz hj) x

/-- `main:eq:smoothing-high`: Taylor remainder for a smooth periodic field, with
exactly `N + 1` input derivatives measured on the shared fundamental cell. -/
theorem IsSmoothPeriodic.norm_sub_cutoffTaylorPolynomial_le {n : ℕ} [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (N : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖periodicLift f (x + y) - cutoffTaylorPolynomial (periodicLift f) (N + 1) x y‖ ≤
      (N.factorial : ℝ)⁻¹ * cNorm (fundamentalCell n) (N + 1) (periodicLift f) *
        ‖y‖ ^ (N + 1) :=
  JanetCartan.norm_sub_cutoffTaylorPolynomial_le hf.2 N
    (hf.norm_iteratedFDeriv_le_cNorm (Nat.le_refl _)) x y

end JanetCartan
