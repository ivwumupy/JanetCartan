module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# A Euclidean Schwartz kernel for the fixed cutoff

For `main:lem:smoothing` and `main:eq:smoothing-high`, take the inverse Fourier
transform of the fixed symbol, with Mathlib's `2π` normalization. The corresponding
periodic convolution uses displacement `(2 * π / R) • y`. All polynomially weighted
absolute moments of this one kernel are finite, with no dependence on `R` or the input.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace JanetCartan

/-- `main:lem:smoothing`: the fixed symbol as a real Schwartz function. -/
def cutoffSchwartzSymbol (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℝ) :=
  hasCompactSupport_fourierCutoff.toSchwartzMap contDiff_fourierCutoff

/-- `main:lem:smoothing`: complexification only for the Euclidean Fourier transform. -/
def cutoffComplexSchwartzSymbol (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (cutoffSchwartzSymbol n)

/-- `main:eq:smoothing-high`: the complex inverse transform of the fixed symbol. -/
def cutoffComplexSchwartzKernel (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  𝓕⁻ (cutoffComplexSchwartzSymbol n)

/-- `main:eq:smoothing-high`: the real kernel used for real vector-valued fields. -/
def cutoffSchwartzKernel (n : ℕ) : 𝓢(EuclideanSpace ℝ (Fin n), ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM (cutoffComplexSchwartzKernel n)

/-- `main:lem:smoothing`: the Schwartz symbol is the already fixed cutoff. -/
@[simp] theorem cutoffSchwartzSymbol_apply (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    cutoffSchwartzSymbol n ξ = fourierCutoff ξ := rfl

/-- `main:lem:smoothing`: complexification leaves the real symbol unchanged. -/
@[simp] theorem cutoffComplexSchwartzSymbol_apply (n : ℕ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    cutoffComplexSchwartzSymbol n ξ = (fourierCutoff ξ : ℂ) := rfl

/-- `main:eq:smoothing-high`: real part of the complex inverse transform. -/
@[simp] theorem cutoffSchwartzKernel_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    cutoffSchwartzKernel n y = (cutoffComplexSchwartzKernel n y).re := rfl

/-- `main:eq:smoothing-high`: Fourier inversion recovers exactly the fixed symbol. -/
theorem fourier_cutoffComplexSchwartzKernel (n : ℕ) :
    𝓕 (cutoffComplexSchwartzKernel n) = cutoffComplexSchwartzSymbol n :=
  FourierTransform.fourier_fourierInv_eq _

/-- `main:eq:smoothing-high`: the symbol is constant on a neighborhood of zero. -/
theorem cutoffComplexSchwartzSymbol_eventuallyEq_one (n : ℕ) :
    (cutoffComplexSchwartzSymbol n : EuclideanSpace ℝ (Fin n) → ℂ) =ᶠ[
      nhds 0] (fun _ ↦ 1) := by
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one] with ξ hξ
  have hξ' : ‖ξ‖ ≤ 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using hξ : ‖ξ‖ < 1).le
  simp [fourierCutoff_eq_one hξ']

/-- `main:eq:smoothing-high`: every positive derivative of the symbol vanishes
at zero, the Fourier-side source of moment cancellation. -/
theorem iteratedFDeriv_cutoffComplexSchwartzSymbol_zero (n j : ℕ) (hj : j ≠ 0) :
    iteratedFDeriv ℝ j (cutoffComplexSchwartzSymbol n) 0 = 0 := by
  rw [((cutoffComplexSchwartzSymbol_eventuallyEq_one n).iteratedFDeriv ℝ j).eq_of_nhds]
  simp [iteratedFDeriv_const_of_ne hj]

/-- `main:eq:smoothing-high`: the complex kernel has unit total mass. -/
theorem integral_cutoffComplexSchwartzKernel (n : ℕ) :
    (∫ y, cutoffComplexSchwartzKernel n y) = 1 := by
  have h := congrArg (fun g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) ↦ g 0)
    (fourier_cutoffComplexSchwartzKernel n)
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq,
    fourierCutoff_eq_one (by simp : ‖(0 : EuclideanSpace ℝ (Fin n))‖ ≤ 1)] using h

/-- `main:eq:smoothing-high`: the real kernel reproduces constants. -/
theorem integral_cutoffSchwartzKernel (n : ℕ) :
    (∫ y, cutoffSchwartzKernel n y) = 1 := by
  change (∫ y, Complex.reCLM (cutoffComplexSchwartzKernel n y)) = 1
  rw [Complex.reCLM.integral_comp_comm (cutoffComplexSchwartzKernel n).integrable,
    integral_cutoffComplexSchwartzKernel]
  rfl

/-- `main:eq:smoothing-high`: all absolute moments of the fixed kernel are integrable. -/
theorem integrable_pow_norm_cutoffSchwartzKernel (n N : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ N * ‖cutoffSchwartzKernel n y‖) :=
  (cutoffSchwartzKernel n).integrable_pow_mul volume N

/-- `main:eq:smoothing-high`: a finite constant independent of the scale and input. -/
def cutoffKernelMoment (n N : ℕ) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ N * ‖cutoffSchwartzKernel n y‖

/-- `main:eq:smoothing-high`: absolute moment constants are nonnegative. -/
theorem cutoffKernelMoment_nonneg (n N : ℕ) : 0 ≤ cutoffKernelMoment n N :=
  integral_nonneg (fun _ ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))

end JanetCartan
