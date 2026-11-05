module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The convolution kernel of the fixed periodic cutoff

For `main:lem:smoothing`, this file identifies the already constructed operator
with convolution by its real finite Fourier kernel. The kernel is independent
of the input field and codomain. Uniform L¹ derivative bounds are separate
analytic obligations; no such bound is assumed in the convolution identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan

variable {n : ℕ}

/-- `main:lem:smoothing`: the real convolution kernel for the fixed symbol. -/
def periodicCutoffKernel (R : ℝ) (x : Torus n) : ℝ :=
  ∑ k ∈ periodicCutoffBox n R, periodicCutoffSymbol R k * (UnitAddTorus.mFourier k x).re

/-- `main:lem:smoothing`: the finite Fourier kernel is continuous. -/
theorem continuous_periodicCutoffKernel (R : ℝ) :
    Continuous (periodicCutoffKernel (n := n) R) := by
  unfold periodicCutoffKernel
  fun_prop

/-- `main:lem:smoothing`: the scalar kernel has a smooth Euclidean lift. -/
theorem contDiff_periodicLift_periodicCutoffKernel (R : ℝ) :
    ContDiff ℝ ∞ (periodicLift (periodicCutoffKernel (n := n) R)) := by
  change ContDiff ℝ ∞ (fun x ↦ ∑ k ∈ periodicCutoffBox n R,
    periodicCutoffSymbol R k * (periodicLift (UnitAddTorus.mFourier k) x).re)
  exact ContDiff.sum (fun k _ ↦
    contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_periodicLift_mFourier k)))

private theorem mFourier_apply_sub (k : Fin n → ℤ) (x y : Torus n) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply,
    fourier_apply, smul_sub, Pi.neg_apply, neg_smul]
  simp only [sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg,
    Circle.coe_mul, Finset.prod_mul_distrib]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem periodicFourierMode_eq_integral {f : Torus n → F}
    (hf : Continuous f) (k : Fin n → ℤ) (x : Torus n) :
    periodicFourierMode k (periodicFourierCoeff f k) x =
      ∫ y, (UnitAddTorus.mFourier k (x - y)).re • f y := by
  have hr : Integrable (fun y ↦
      (UnitAddTorus.mFourier k x).re • ((UnitAddTorus.mFourier (-k) y).re • f y)) :=
    (continuous_const.smul
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun y ↦
      (UnitAddTorus.mFourier k x).im • ((UnitAddTorus.mFourier (-k) y).im • f y)) :=
    (continuous_const.smul
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [mFourier_apply_sub, Complex.mul_re, sub_smul, mul_smul]
  rw [integral_sub hr hi, integral_smul, integral_smul]
  rfl

/-- `main:lem:smoothing`: the actual vector-valued cutoff is convolution by the
one fixed scalar kernel. This identity uses the shared `2π` Fourier convention. -/
theorem periodicCutoff_eq_integral_kernel {f : Torus n → F}
    (hf : Continuous f) (R : ℝ) (x : Torus n) :
    periodicCutoff R f x = ∫ y, periodicCutoffKernel R (x - y) • f y := by
  have hint (k : Fin n → ℤ) : Integrable (fun y ↦
      (periodicCutoffSymbol R k * (UnitAddTorus.mFourier k (x - y)).re) • f y) :=
    (continuous_const.mul (Complex.continuous_re.comp
      ((UnitAddTorus.mFourier k).continuous.comp (continuous_const.sub continuous_id)))
      |>.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [periodicCutoffKernel, Finset.sum_smul]
  rw [integral_finsetSum _ (fun k _ ↦ hint k)]
  unfold periodicCutoff
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_smul, integral_smul, periodicFourierMode_eq_integral hf]

/-- `main:lem:smoothing`: convolution bounds the actual cutoff by the L¹ mass
of its kernel. A bound on that mass independent of `R` is still needed for C⁰ smoothing. -/
theorem norm_periodicCutoff_le_kernel_mass {f : Torus n → F}
    (hf : Continuous f) {A : ℝ} (hbound : ∀ y, ‖f y‖ ≤ A) (R : ℝ) (x : Torus n) :
    ‖periodicCutoff R f x‖ ≤ (∫ y, ‖periodicCutoffKernel (n := n) R y‖) * A := by
  let : Measure.IsNegInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isNegInvariant _
  let : Measure.IsAddLeftInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isAddLeftInvariant _
  rw [periodicCutoff_eq_integral_kernel hf]
  calc
    _ ≤ ∫ y, ‖periodicCutoffKernel R (x - y)‖ * A := by
      apply norm_integral_le_of_norm_le
        (((continuous_periodicCutoffKernel R).comp (continuous_const.sub continuous_id)
          |>.norm.mul continuous_const).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      exact Filter.Eventually.of_forall (fun y ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    _ = _ := by
      rw [integral_mul_const,
        integral_sub_left_eq_self (fun y ↦ ‖periodicCutoffKernel R y‖) volume x]

end JanetCartan
