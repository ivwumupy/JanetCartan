module

public import JanetCartan.Analysis.Fourier.LatticeQuadrature.Window
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fourier zeros of convolution windows

The polynomial cancellation argument of `app:ch_waves:thm:sampling` in paper.tex,
with the unit-period Fourier convention.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform Convolution ContDiff

namespace JanetCartan.LatticeQuadrature

/-- Complexification commutes with real convolution, used for the windows in
`app:ch_waves:thm:sampling`. -/
theorem ofReal_convolution (f g : ℝ → ℝ) :
    (fun x ↦ ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x : ℂ)) =
      (fun x ↦ (f x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x ↦ (g x : ℂ)) := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]

/-- The centered box has zero Fourier transform at every nonzero integer
(`app:ch_waves:thm:sampling`). -/
theorem fourier_unitBox_int {k : ℤ} (hk : k ≠ 0) :
    𝓕 (fun x ↦ (unitBox x : ℂ)) (k : ℝ) = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have heq : (fun v : ℝ ↦ Complex.exp ((-2 * Real.pi * v * (k : ℝ) : ℝ) * Complex.I) •
      (unitBox v : ℂ)) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (fun v ↦ fourier (-k) (v : UnitAddCircle)) := by
    funext v
    by_cases hv : v ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · simp only [unitBox, indicator_of_mem hv, Complex.ofReal_one, smul_eq_mul, mul_one,
        fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
        Complex.ofReal_intCast, Int.cast_neg, Complex.ofReal_one, div_one]
      congr 1; ring
    · simp only [unitBox, indicator_of_notMem hv, Complex.ofReal_zero, smul_zero]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) k
  rw [fourierCoeff_eq_intervalIntegral _ _ (-(1 / 2 : ℝ))] at h
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  simpa [hk, Pi.single_apply] using h

/-- Compact support gives smoothness of the box Fourier transform despite the
endpoint discontinuities of the box (`app:ch_waves:thm:sampling`). -/
theorem contDiff_fourier_unitBox :
    ContDiff ℝ ∞ (𝓕 (fun x ↦ (unitBox x : ℂ))) := by
  apply Real.contDiff_fourier
  intro n _
  have heq : (fun x : ℝ ↦ ‖x‖ ^ n * ‖(unitBox x : ℂ)‖) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x ↦ ‖x‖ ^ n) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · simp only [unitBox, indicator_of_mem hx, Complex.ofReal_one, norm_one, mul_one]
    · simp only [unitBox, indicator_of_notMem hx, Complex.ofReal_zero, norm_zero, mul_zero]
  rw [heq, integrable_indicator_iff measurableSet_Icc]
  exact (continuous_norm.pow n).integrableOn_Icc

/-- All moments of a continuous compactly supported function are integrable,
so its Fourier transform is smooth (`app:ch_waves:thm:sampling`). -/
theorem contDiff_fourier_of_continuous_hasCompactSupport {f : ℝ → ℂ}
    (hc : HasCompactSupport f) (hs : Continuous f) : ContDiff ℝ ∞ (𝓕 f) := by
  apply Real.contDiff_fourier
  intro n _
  exact ((continuous_norm.pow n).mul hs.norm).integrable_of_hasCompactSupport
    hc.norm.mul_left

/-- Each box factor multiplies the Fourier transform by the box transform
(`app:ch_waves:thm:sampling`). -/
theorem fourier_convolvedBoxWindow_succ {κ : ℝ → ℝ} (hκ : Integrable κ) (q : ℕ) :
    𝓕 (fun x ↦ (convolvedBoxWindow κ (q + 1) x : ℂ)) =
      𝓕 (fun x ↦ (convolvedBoxWindow κ q x : ℂ)) * 𝓕 (fun x ↦ (unitBox x : ℂ)) := by
  rw [convolvedBoxWindow, ofReal_convolution]
  funext ξ
  exact Real.fourier_mul_convolution_eq
    (integrable_convolvedBoxWindow hκ q).ofReal integrable_unitBox.ofReal ξ

/-- The order-`q` window has Fourier zeros of order at least `q` at nonzero
integers, as required in `app:ch_waves:thm:sampling`. -/
theorem iteratedDeriv_fourier_convolvedBoxWindow_int {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q j : ℕ} (hj : j < q)
    {k : ℤ} (hk : k ≠ 0) :
    iteratedDeriv j (𝓕 (fun x ↦ (convolvedBoxWindow κ q x : ℂ))) (k : ℝ) = 0 := by
  induction q generalizing j with
  | zero => omega
  | succ q ih =>
    rw [fourier_convolvedBoxWindow_succ (hs.continuous.integrable_of_hasCompactSupport hc)]
    have hcw : ContDiff ℝ ∞ (𝓕 (fun x ↦ (convolvedBoxWindow κ q x : ℂ))) :=
      contDiff_fourier_of_continuous_hasCompactSupport
        ((hasCompactSupport_convolvedBoxWindow hc q).comp_left Complex.ofReal_zero)
        (Complex.continuous_ofReal.comp (contDiff_convolvedBoxWindow hc hs q).continuous)
    rw [iteratedDeriv_mul (hcw.of_le (by simp)).contDiffAt
      (contDiff_fourier_unitBox.of_le (by simp)).contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hiq : i < q
    · rw [ih hiq, mul_zero, zero_mul]
    · have hij : j - i = 0 := by omega
      simp only [hij, iteratedDeriv_zero, fourier_unitBox_int hk, mul_zero]

/-- Multiplication by a monomial of degree below `q` preserves the nonzero
integer Fourier zeros of the window (`app:ch_waves:thm:sampling`). -/
theorem fourier_monomial_convolvedBoxWindow_int {κ : ℝ → ℝ}
    (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) {q j : ℕ} (hj : j < q)
    {k : ℤ} (hk : k ≠ 0) :
    𝓕 (fun x : ℝ ↦ (x : ℂ) ^ j * (convolvedBoxWindow κ q x : ℂ)) (k : ℝ) = 0 := by
  have hc' : HasCompactSupport (fun x ↦ (convolvedBoxWindow κ q x : ℂ)) :=
    (hasCompactSupport_convolvedBoxWindow hc q).comp_left Complex.ofReal_zero
  have hs' : Continuous (fun x ↦ (convolvedBoxWindow κ q x : ℂ)) :=
    Complex.continuous_ofReal.comp (contDiff_convolvedBoxWindow hc hs q).continuous
  have hi (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n • (convolvedBoxWindow κ q x : ℂ)) :=
    ((continuous_id.pow n).smul hs').integrable_of_hasCompactSupport hc'.smul_left
  have hd := congrFun (Real.iteratedDeriv_fourier (N := ⊤) (fun n _ ↦ hi n)
    (n := j) (by simp)) (k : ℝ)
  have heq : (fun x : ℝ ↦ (-2 * (Real.pi : ℂ) * Complex.I * x) ^ j •
      (convolvedBoxWindow κ q x : ℂ)) =
      (-2 * (Real.pi : ℂ) * Complex.I) ^ j •
        (fun x : ℝ ↦ (x : ℂ) ^ j * (convolvedBoxWindow κ q x : ℂ)) := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_assoc]
  rw [iteratedDeriv_fourier_convolvedBoxWindow_int hc hs hj hk, heq,
    show 𝓕 ((-2 * (Real.pi : ℂ) * Complex.I) ^ j •
      (fun x : ℝ ↦ (x : ℂ) ^ j * (convolvedBoxWindow κ q x : ℂ))) =
      (-2 * (Real.pi : ℂ) * Complex.I) ^ j •
        𝓕 (fun x : ℝ ↦ (x : ℂ) ^ j * (convolvedBoxWindow κ q x : ℂ)) from
      VectorFourier.fourierIntegral_const_smul _ _ _ _ _] at hd
  have hne : (-2 * (Real.pi : ℂ) * Complex.I) ^ j ≠ 0 := by
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact (mul_eq_zero.mp hd.symm).resolve_left hne

end JanetCartan.LatticeQuadrature
