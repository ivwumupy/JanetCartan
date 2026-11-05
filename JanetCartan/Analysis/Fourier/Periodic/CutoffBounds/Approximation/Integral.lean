module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.SchwartzKernel
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Taylor

/-!
# Integrating the Taylor remainder against the cutoff kernel

The estimates in this file are the analytic Taylor step of `main:eq:smoothing-high`.
The Euclidean integral operator is defined from the fixed Schwartz kernel. Its
identification with `periodicCutoff`, and cancellation of the nonconstant Taylor
terms, are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:smoothing-high`: polynomial growth is integrable against the actual
Schwartz kernel, including constant bounds when `N = 0`. -/
theorem integrable_cutoffSchwartzKernel_smul_of_norm_le {g : EuclideanSpace ℝ (Fin n) → F}
    (hg : Continuous g) (N : ℕ) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M * ‖y‖ ^ N) :
    Integrable (fun y ↦ cutoffSchwartzKernel n y • g y) := by
  apply ((integrable_pow_norm_cutoffSchwartzKernel n N).mul_const M).mono'
    ((cutoffSchwartzKernel n).continuous.smul hg).aestronglyMeasurable
  filter_upwards [] with y
  change ‖cutoffSchwartzKernel n y • g y‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖cutoffSchwartzKernel n y‖ * (M * ‖y‖ ^ N) :=
      mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)
    _ = _ := by ring

/-- `main:eq:smoothing-high`: every homogeneous Taylor term is integrable,
including arbitrary real displacement scales. -/
theorem integrable_cutoffSchwartzKernel_smul_multilinear (j : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F)
    (a : ℝ) :
    Integrable (fun y ↦ cutoffSchwartzKernel n y • A (fun _ ↦ a • y)) := by
  apply integrable_cutoffSchwartzKernel_smul_of_norm_le (by fun_prop) j
    (M := ‖A‖ * |a| ^ j)
  intro y
  calc
    _ ≤ ‖A‖ * ∏ _ : Fin j, ‖a • y‖ := A.le_opNorm _
    _ = _ := by simp [norm_smul, Real.norm_eq_abs, mul_pow, mul_assoc]

/-- `main:eq:smoothing-high`: the entire finite Taylor polynomial is integrable
against the fixed kernel, without any smoothness assumption on its coefficients. -/
theorem integrable_cutoffSchwartzKernel_smul_taylor (f : EuclideanSpace ℝ (Fin n) → F)
    (N : ℕ) (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Integrable (fun y ↦ cutoffSchwartzKernel n y • cutoffTaylorPolynomial f N x (a • y)) := by
  simp only [cutoffTaylorPolynomial, Finset.smul_sum, smul_comm (cutoffSchwartzKernel n _)]
  apply integrable_finsetSum
  intro j _
  exact (integrable_cutoffSchwartzKernel_smul_multilinear j (iteratedFDeriv ℝ j f x) a).smul _

/-- `main:eq:smoothing-high`: Euclidean convolution with the fixed symbol's inverse
transform, at the displacement dictated by the unit-torus `2π` convention. -/
def cutoffEuclideanConvolution (R : ℝ) (f : Torus n → F)
    (x : EuclideanSpace ℝ (Fin n)) : F :=
  ∫ y, cutoffSchwartzKernel n y • periodicLift f (x - (2 * Real.pi / R) • y)

/-- `main:eq:smoothing-high`: the Euclidean convolution is an integrable Bochner integral. -/
theorem integrable_cutoffEuclideanConvolution {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦
      cutoffSchwartzKernel n y • periodicLift f (x - (2 * Real.pi / R) • y)) := by
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦
      periodicLift f (x - (2 * Real.pi / R) • y)) :=
    hf.2.continuous.comp (continuous_const.sub (continuous_id.const_smul (2 * Real.pi / R)))
  apply integrable_cutoffSchwartzKernel_smul_of_norm_le hc 0
    (M := cNorm (fundamentalCell n) 0 (periodicLift f))
  intro y
  simpa using hf.norm_iteratedFDeriv_le_cNorm (Nat.le_refl 0) (x - (2 * Real.pi / R) • y)

/-- `main:eq:smoothing-high`: the integral of the Taylor remainder has precisely
`N + 1` powers of the displacement scale and uses precisely `N + 1` derivatives. -/
theorem norm_integral_cutoffTaylorRemainder_le [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (N : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    ‖∫ y, cutoffSchwartzKernel n y •
      (periodicLift f (x + a • y) -
        cutoffTaylorPolynomial (periodicLift f) (N + 1) x (a • y))‖ ≤
      cutoffKernelMoment n (N + 1) * |a| ^ (N + 1) * (N.factorial : ℝ)⁻¹ *
        cNorm (fundamentalCell n) (N + 1) (periodicLift f) := by
  let B := |a| ^ (N + 1) * (N.factorial : ℝ)⁻¹ *
    cNorm (fundamentalCell n) (N + 1) (periodicLift f)
  calc
    _ ≤ ∫ y : EuclideanSpace ℝ (Fin n),
        (‖y‖ ^ (N + 1) * ‖cutoffSchwartzKernel n y‖) * B := by
      apply norm_integral_le_of_norm_le
        ((integrable_pow_norm_cutoffSchwartzKernel n (N + 1)).mul_const B)
      filter_upwards [] with y
      rw [norm_smul]
      calc
        _ ≤ ‖cutoffSchwartzKernel n y‖ *
            ((N.factorial : ℝ)⁻¹ * cNorm (fundamentalCell n) (N + 1) (periodicLift f) *
              ‖a • y‖ ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left (hf.norm_sub_cutoffTaylorPolynomial_le N x (a • y))
            (norm_nonneg _)
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, mul_pow]; dsimp [B]; ring
    _ = _ := by rw [integral_mul_const]; dsimp [B, cutoffKernelMoment]; ring

/-- `main:eq:smoothing-high`: a concrete nonnegative constant for positive orders. -/
def cutoffTaylorErrorConstant (n N : ℕ) : ℝ :=
  cutoffKernelMoment n (N + 1) * (2 * Real.pi) ^ (N + 1) * (N.factorial : ℝ)⁻¹

/-- `main:eq:smoothing-high`: the positive-order constant is nonnegative. -/
theorem cutoffTaylorErrorConstant_nonneg (n N : ℕ) : 0 ≤ cutoffTaylorErrorConstant n N := by
  unfold cutoffTaylorErrorConstant
  exact mul_nonneg (mul_nonneg (cutoffKernelMoment_nonneg _ _) (by positivity)) (by positivity)

/-- `main:eq:smoothing-high`: the Taylor integral remainder has the required
`R⁻⁽ᴺ⁺¹⁾` decay, without any loss depending on the dimension. -/
theorem norm_integral_cutoffTaylorRemainder_scaled_le [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (N : ℕ)
    {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    ‖∫ y, cutoffSchwartzKernel n y •
      (periodicLift f (x - (2 * Real.pi / R) • y) -
        cutoffTaylorPolynomial (periodicLift f) (N + 1) x (-(2 * Real.pi / R) • y))‖ ≤
      cutoffTaylorErrorConstant n N * (R ^ (N + 1))⁻¹ *
        cNorm (fundamentalCell n) (N + 1) (periodicLift f) := by
  have h := norm_integral_cutoffTaylorRemainder_le hf N x (-(2 * Real.pi / R))
  simp only [neg_smul, ← sub_eq_add_neg] at h
  convert h using 1
  · simp only [neg_smul]
  · rw [abs_neg, abs_of_pos (div_pos (by positivity) hR), div_pow]
    dsimp [cutoffTaylorErrorConstant]
    ring

/-- `main:eq:smoothing-high`: order zero requires no cancellation beyond unit
mass and has a uniform bound for the Euclidean convolution error. -/
theorem norm_sub_cutoffEuclideanConvolution_zero_le [CompleteSpace F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖periodicLift f x - cutoffEuclideanConvolution R f x‖ ≤
      (1 + cutoffKernelMoment n 0) * cNorm (fundamentalCell n) 0 (periodicLift f) := by
  have hb (z : EuclideanSpace ℝ (Fin n)) :
      ‖periodicLift f z‖ ≤ cNorm (fundamentalCell n) 0 (periodicLift f) := by
    simpa using hf.norm_iteratedFDeriv_le_cNorm (Nat.le_refl 0) z
  have hi : ‖cutoffEuclideanConvolution R f x‖ ≤
      cutoffKernelMoment n 0 * cNorm (fundamentalCell n) 0 (periodicLift f) := by
    unfold cutoffEuclideanConvolution
    calc
      _ ≤ ∫ y, ‖cutoffSchwartzKernel n y‖ *
          cNorm (fundamentalCell n) 0 (periodicLift f) := by
        apply norm_integral_le_of_norm_le
          ((cutoffSchwartzKernel n).integrable.norm.mul_const _)
        filter_upwards [] with y
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
      _ = _ := by simp [integral_mul_const, cutoffKernelMoment]
  calc
    _ ≤ ‖periodicLift f x‖ + ‖cutoffEuclideanConvolution R f x‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith [hb x]

end JanetCartan
