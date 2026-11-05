module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Moments
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Realization

/-!
# Sharp approximation by the fixed periodic cutoff

For `main:lem:smoothing` and `main:eq:smoothing-high`, the fixed `periodicCutoff`
has pointwise approximation error bounded by `C_N * R⁻ᴺ` times the input Cᴺ norm
on the fundamental cell. The constant depends only on the dimension and order,
and the same cutoff works at every order, including zero.

The proof combines the Euclidean convolution identity with polynomial cancellation
and the Taylor remainder bound. There is no dimension-dependent derivative loss.
The pointwise bound holds for real Banach codomains; the final existence statement
specializes it to finite-dimensional real normed spaces.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

/-- `main:eq:smoothing-high`: a constant for every approximation order, independent
of the scale, input field, and codomain. Order zero uses the kernel's absolute mass. -/
def periodicCutoffApproximationConstant (n : ℕ) : ℕ → ℝ
  | 0 => 1 + cutoffKernelMoment n 0
  | N + 1 => cutoffTaylorErrorConstant n N

/-- `main:eq:smoothing-high`: the approximation constants are nonnegative. -/
theorem periodicCutoffApproximationConstant_nonneg (n N : ℕ) :
    0 ≤ periodicCutoffApproximationConstant n N := by
  cases N with
  | zero => exact add_nonneg zero_le_one (cutoffKernelMoment_nonneg n 0)
  | succ N => exact cutoffTaylorErrorConstant_nonneg n N

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Banach

variable [CompleteSpace F]

/-- `main:eq:smoothing-high`: cancellation turns the Euclidean convolution error
into the Taylor remainder, using exactly `N + 1` input derivatives. -/
theorem norm_sub_cutoffEuclideanConvolution_succ_le {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (N : ℕ) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖periodicLift f x - cutoffEuclideanConvolution R f x‖ ≤
      cutoffTaylorErrorConstant n N * (R ^ (N + 1))⁻¹ *
        cNorm (fundamentalCell n) (N + 1) (periodicLift f) := by
  have h := norm_integral_cutoffTaylorRemainder_scaled_le hf N hR x
  simp_rw [smul_sub] at h
  rw [integral_sub (integrable_cutoffEuclideanConvolution hf R x)
    (integrable_cutoffSchwartzKernel_smul_taylor (periodicLift f) (N + 1) x
      (-(2 * Real.pi / R))),
    integral_cutoffSchwartzKernel_smul_taylor (periodicLift f) (N + 1)
      (Nat.succ_pos N)] at h
  rw [norm_sub_rev]
  exact h

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: the lifted approximation bound
for the actual fixed cutoff, at every natural order and every positive scale. -/
theorem norm_periodicLift_sub_periodicCutoff_le {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (N : ℕ) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖periodicLift f x - periodicLift (periodicCutoff R f) x‖ ≤
      periodicCutoffApproximationConstant n N * (R ^ N)⁻¹ *
        cNorm (fundamentalCell n) N (periodicLift f) := by
  rw [← cutoffEuclideanConvolution_eq_periodicCutoff hf hR x]
  cases N with
  | zero =>
      simpa only [periodicCutoffApproximationConstant, pow_zero, inv_one, mul_one] using
        norm_sub_cutoffEuclideanConvolution_zero_le hf R x
  | succ N => exact norm_sub_cutoffEuclideanConvolution_succ_le hf N hR x

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: pointwise error on the quotient
torus, with exactly `N` derivatives and `R⁻ᴺ` decay for the same cutoff at all orders. -/
theorem norm_sub_periodicCutoff_le {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (N : ℕ) {R : ℝ} (hR : 0 < R) (x : Torus n) :
    ‖f x - periodicCutoff R f x‖ ≤
      periodicCutoffApproximationConstant n N * (R ^ N)⁻¹ *
        cNorm (fundamentalCell n) N (periodicLift f) := by
  classical
  choose a ha using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  have hy : torusQuotient y = x := by
    funext i
    exact ha i
  simpa only [periodicLift, Function.comp_apply, hy] using
    norm_periodicLift_sub_periodicCutoff_le hf N hR y

end Banach

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: for every finite-dimensional
real normed codomain and every `N`, a nonnegative constant independent of `R` and
`f` bounds the approximation error by `R⁻ᴺ` times exactly the Cᴺ input norm. -/
theorem exists_periodicCutoff_approximation_bound [FiniteDimensional ℝ F] (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (f : Torus n → F),
      IsSmoothPeriodic f → ∀ x : Torus n,
        ‖f x - periodicCutoff R f x‖ ≤
          C * (R ^ N)⁻¹ * cNorm (fundamentalCell n) N (periodicLift f) := by
  refine ⟨periodicCutoffApproximationConstant n N,
    periodicCutoffApproximationConstant_nonneg n N, ?_⟩
  intro R hR f hf x
  exact norm_sub_periodicCutoff_le hf N (lt_of_lt_of_le zero_lt_one hR) x

end JanetCartan
