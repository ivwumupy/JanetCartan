module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Convolved box windows

The window used in `app:ch_waves:thm:sampling` of paper.tex is obtained by
convolving a smooth unit-mass kernel with `q` centered unit boxes. The closed
box has the manuscript's endpoints; endpoints are immaterial for convolution.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Convolution ContDiff

namespace JanetCartan.LatticeQuadrature

/-- The centered unit box from `app:ch_waves:thm:sampling`. -/
def unitBox : ℝ → ℝ := (Icc (-(1 / 2)) (1 / 2)).indicator (fun _ ↦ 1)

/-- The window with `q` box factors in `app:ch_waves:thm:sampling`.
The zero-order window is the original smoothing kernel. -/
def convolvedBoxWindow (κ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => κ
  | q + 1 => convolvedBoxWindow κ q ⋆[ContinuousLinearMap.mul ℝ ℝ] unitBox

/-- The unit box in `app:ch_waves:thm:sampling` is integrable. -/
theorem integrable_unitBox : Integrable unitBox :=
  (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

/-- The unit box in `app:ch_waves:thm:sampling` has compact support. -/
theorem hasCompactSupport_unitBox : HasCompactSupport unitBox :=
  HasCompactSupport.intro isCompact_Icc fun _ hx ↦ indicator_of_notMem hx _

/-- The unit box in `app:ch_waves:thm:sampling` has mass one. -/
theorem integral_unitBox : ∫ x, unitBox x = 1 := by
  rw [unitBox, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  norm_num

/-- Integrability of the convolution windows in `app:ch_waves:thm:sampling`. -/
theorem integrable_convolvedBoxWindow {κ : ℝ → ℝ} (hκ : Integrable κ) (q : ℕ) :
    Integrable (convolvedBoxWindow κ q) := by
  induction q with
  | zero => exact hκ
  | succ q ih => exact ih.integrable_convolution _ integrable_unitBox

/-- Convolving with unit boxes preserves mass (`app:ch_waves:thm:sampling`). -/
theorem integral_convolvedBoxWindow {κ : ℝ → ℝ} (hκ : Integrable κ) (q : ℕ) :
    ∫ x, convolvedBoxWindow κ q x = ∫ x, κ x := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [convolvedBoxWindow, integral_convolution _ (integrable_convolvedBoxWindow hκ q)
      integrable_unitBox, integral_unitBox]
    simpa using ih

/-- Compact support of the windows in `app:ch_waves:thm:sampling`. -/
theorem hasCompactSupport_convolvedBoxWindow {κ : ℝ → ℝ}
    (hκ : HasCompactSupport κ) (q : ℕ) : HasCompactSupport (convolvedBoxWindow κ q) := by
  induction q with
  | zero => exact hκ
  | succ q ih => exact ih.convolution _ hasCompactSupport_unitBox

/-- Smoothness is supplied by the smoothing kernel in `app:ch_waves:thm:sampling`. -/
theorem contDiff_convolvedBoxWindow {κ : ℝ → ℝ} (hc : HasCompactSupport κ)
    (hs : ContDiff ℝ ∞ κ) (q : ℕ) : ContDiff ℝ ∞ (convolvedBoxWindow κ q) := by
  induction q with
  | zero => exact hs
  | succ q ih =>
    exact (hasCompactSupport_convolvedBoxWindow hc q).contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℝ) ih integrable_unitBox.locallyIntegrable

/-- Positivity of the window in `app:ch_waves:thm:sampling`. -/
theorem convolvedBoxWindow_nonneg {κ : ℝ → ℝ} (hκ : ∀ x, 0 ≤ κ x) (q : ℕ) (x : ℝ) :
    0 ≤ convolvedBoxWindow κ q x := by
  induction q generalizing x with
  | zero => exact hκ x
  | succ q ih =>
    apply integral_nonneg
    intro t
    exact mul_nonneg (ih t) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)

/-- A box convolution is a moving unit-interval average
(`app:ch_waves:thm:sampling`). No continuity assumption is needed. -/
theorem convolution_unitBox_eq_intervalIntegral (f : ℝ → ℝ) (x : ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] unitBox) x =
      ∫ t in x - 1 / 2..x + 1 / 2, f t := by
  rw [convolution_mul_swap]
  have heq : (fun t ↦ f (x - t) * unitBox t) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun t ↦ f (x - t)) := by
    funext t
    simpa only [unitBox, mul_one] using
      (indicator_mul_right (Icc (-(1 / 2 : ℝ)) (1 / 2))
        (fun t ↦ f (x - t)) (fun _ ↦ (1 : ℝ)) (i := t)).symm
  rw [heq]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_comp_sub_left]
  congr 1; ring

/-- Translated box averages sum to the original mass
(`app:ch_waves:thm:sampling`). `HasSum` records actual convergence. -/
theorem hasSum_convolution_unitBox {f : ℝ → ℝ} (hf : Integrable f) (u : ℝ) :
    HasSum (fun m : ℤ ↦ (f ⋆[ContinuousLinearMap.mul ℝ ℝ] unitBox) (u + m))
      (∫ x, f x) := by
  simp_rw [convolution_unitBox_eq_intervalIntegral]
  convert hf.hasSum_intervalIntegral (u - 1 / 2) using 1
  funext m
  congr 1 <;> ring

/-- Every positive-order window gives a translated partition of unity when the
kernel has mass one (`app:ch_waves:thm:sampling`). -/
theorem hasSum_convolvedBoxWindow {κ : ℝ → ℝ} (hκ : Integrable κ)
    (hm : ∫ x, κ x = 1) {q : ℕ} (hq : 0 < q) (u : ℝ) :
    HasSum (fun m : ℤ ↦ convolvedBoxWindow κ q (u + m)) 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simpa only [convolvedBoxWindow, integral_convolvedBoxWindow hκ, hm] using
    hasSum_convolution_unitBox (integrable_convolvedBoxWindow hκ r) u

/-- The support radius increases by one half for each box factor
(`app:ch_waves:thm:sampling`). Taking `a = 1/4` gives length at most `q + 1/2`. -/
theorem support_convolvedBoxWindow_subset {κ : ℝ → ℝ} {a : ℝ}
    (hκ : Function.support κ ⊆ Icc (-a) a) (q : ℕ) :
    Function.support (convolvedBoxWindow κ q) ⊆
      Icc (-a - q / 2) (a + q / 2) := by
  induction q with
  | zero => simpa [convolvedBoxWindow] using hκ
  | succ q ih =>
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx
    have hy' := ih hy
    have hz' : z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := support_indicator_subset hz
    constructor <;> push_cast <;> linarith [hy'.1, hy'.2, hz'.1, hz'.2]

end JanetCartan.LatticeQuadrature
