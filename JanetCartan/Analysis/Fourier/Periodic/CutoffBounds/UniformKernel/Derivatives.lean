module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Derivative kernels for the fixed periodic cutoff

The kernel representation for `main:lem:smoothing` and `main:eq:smoothing-low`
is valid in every complete real normed codomain. The finite Fourier formula
also supplies continuity and integrability of the derivative kernels. The
uniform estimate for their L¹ masses is a separate analytic step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan

variable {n : ℕ}

/-- `main:lem:smoothing`: the scalar multilinear derivative kernel, expanded
using the real and imaginary parts of the unit-torus characters. -/
def periodicCutoffDerivKernel (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Torus n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℝ :=
  ∑ k ∈ periodicCutoffBox n R, periodicCutoffSymbol R k •
    ((UnitAddTorus.mFourier (-k) y).re •
      iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).re) x -
    (UnitAddTorus.mFourier (-k) y).im •
      iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).im) x)

/-- `main:lem:smoothing`: continuity in the integration variable. -/
theorem continuous_periodicCutoffDerivKernel (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Continuous (periodicCutoffDerivKernel j R x) := by
  unfold periodicCutoffDerivKernel
  fun_prop

/-- `main:lem:smoothing`: every derivative kernel has finite L¹ mass. -/
theorem integrable_norm_periodicCutoffDerivKernel (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ ‖periodicCutoffDerivKernel j R x y‖) :=
  (continuous_periodicCutoffDerivKernel j R x).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem iteratedFDeriv_sub_fun_apply {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {j : ℕ} {f g : E → G} {x : E}
    (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x) :
    iteratedFDeriv ℝ j (fun z ↦ f z - g z) x =
      iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x :=
  iteratedFDeriv_sub_apply hf hg

private theorem contDiff_re_character (k : Fin n → ℤ) (j : ℕ) :
    ContDiff ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).re) :=
  (Complex.reCLM.contDiff.comp (contDiff_periodicLift_mFourier k)).of_le (by simp)

private theorem contDiff_im_character (k : Fin n → ℤ) (j : ℕ) :
    ContDiff ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).im) :=
  (Complex.imCLM.contDiff.comp (contDiff_periodicLift_mFourier k)).of_le (by simp)

private theorem character_sub (k : Fin n → ℤ) (x y : Torus n) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply,
    fourier_apply, smul_sub, Pi.neg_apply, neg_smul]
  simp only [sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg,
    Circle.coe_mul, Finset.prod_mul_distrib]

/-- `main:lem:smoothing`: the expanded kernel is exactly the Euclidean
Fréchet derivative of the translated, previously defined convolution kernel. -/
theorem periodicCutoffDerivKernel_eq_iteratedFDeriv (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Torus n) :
    periodicCutoffDerivKernel j R x y =
      iteratedFDeriv ℝ j (fun z ↦ periodicCutoffKernel R (torusQuotient z - y)) x := by
  have heq : (fun z ↦ periodicCutoffKernel R (torusQuotient z - y)) =
      fun z ↦ ∑ k ∈ periodicCutoffBox n R, periodicCutoffSymbol R k •
        ((UnitAddTorus.mFourier (-k) y).re •
            (periodicLift (UnitAddTorus.mFourier k) z).re -
         (UnitAddTorus.mFourier (-k) y).im •
            (periodicLift (UnitAddTorus.mFourier k) z).im) := by
    funext z
    unfold periodicCutoffKernel
    apply Finset.sum_congr rfl
    intro k _
    simp only [character_sub, Complex.mul_re, smul_eq_mul, periodicLift,
      Function.comp_apply]
    ring
  rw [heq, iteratedFDeriv_fun_sum_apply]
  · unfold periodicCutoffDerivKernel
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedFDeriv_const_smul_apply', iteratedFDeriv_sub_fun_apply,
      iteratedFDeriv_const_smul_apply', iteratedFDeriv_const_smul_apply']
    all_goals first
    | exact ((contDiff_re_character k j).contDiffAt)
    | exact ((contDiff_im_character k j).contDiffAt)
    | exact (contDiff_re_character k j).contDiffAt.const_smul _
    | exact (contDiff_im_character k j).contDiffAt.const_smul _
    | exact ((contDiff_re_character k j).contDiffAt.const_smul _).sub
        ((contDiff_im_character k j).contDiffAt.const_smul _)
  · intro k _
    exact (((contDiff_re_character k j).contDiffAt.const_smul _).sub
      ((contDiff_im_character k j).contDiffAt.const_smul _)).const_smul _

/-- `main:lem:smoothing`: changing the evaluation point translates the integration
variable of the derivative kernel. -/
theorem periodicCutoffDerivKernel_translate (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Torus n) :
    periodicCutoffDerivKernel j R x y =
      periodicCutoffDerivKernel j R 0 (y - torusQuotient x) := by
  rw [periodicCutoffDerivKernel_eq_iteratedFDeriv,
    periodicCutoffDerivKernel_eq_iteratedFDeriv]
  have heq : (fun z ↦ periodicCutoffKernel R (torusQuotient z - (y - torusQuotient x))) =
      fun z ↦ periodicCutoffKernel R (torusQuotient (z + x) - y) := by
    funext z
    congr 1
    ext i
    change (z i : AddCircle (1 : ℝ)) - (y i - (x i : AddCircle (1 : ℝ))) =
      ((z i + x i : ℝ) : AddCircle (1 : ℝ)) - y i
    rw [AddCircle.coe_add]
    abel
  rw [heq, iteratedFDeriv_comp_add_right
    (f := fun z ↦ periodicCutoffKernel R (torusQuotient z - y)), zero_add]

/-- `main:lem:smoothing`: the L¹ mass of the derivative kernel is independent
of the Euclidean evaluation point. Thus a uniform mass estimate need only be
proved at the origin. -/
theorem integral_norm_periodicCutoffDerivKernel_eq (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y, ‖periodicCutoffDerivKernel j R x y‖) =
      ∫ y, ‖periodicCutoffDerivKernel (n := n) j R 0 y‖ := by
  let : Measure.IsAddRightInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isAddRightInvariant _
  simp_rw [periodicCutoffDerivKernel_translate j R x]
  exact integral_sub_right_eq_self (μ := volume)
    (fun y : Torus n ↦ ‖periodicCutoffDerivKernel j R 0 y‖) (torusQuotient x)

/-- `main:lem:smoothing`: order zero recovers the mass of the original scalar
convolution kernel, with the unit-torus normalization unchanged. -/
theorem integral_norm_periodicCutoffDerivKernel_zero (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y, ‖periodicCutoffDerivKernel 0 R x y‖) =
      ∫ y, ‖periodicCutoffKernel (n := n) R y‖ := by
  let : Measure.IsNegInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isNegInvariant _
  let : Measure.IsAddLeftInvariant (volume : Measure (Torus n)) :=
    Measure.pi.isAddLeftInvariant _
  simp_rw [periodicCutoffDerivKernel_eq_iteratedFDeriv, norm_iteratedFDeriv_zero]
  exact integral_sub_left_eq_self (fun y : Torus n ↦ ‖periodicCutoffKernel R y‖)
    volume (torusQuotient x)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:smoothing`: the derivative kernel acting on any real normed codomain. -/
def periodicCutoffDerivOperatorKernel (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Torus n) :
    F →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F :=
  ContinuousMultilinearMap.smulRightL ℝ _ F (periodicCutoffDerivKernel j R x y)

/-- `main:lem:smoothing`: the operator kernel is bounded by its scalar
multilinear kernel, independently of the codomain. -/
theorem norm_periodicCutoffDerivOperatorKernel_le (j : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Torus n) :
    ‖periodicCutoffDerivOperatorKernel (F := F) j R x y‖ ≤
      ‖periodicCutoffDerivKernel j R x y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact le_of_eq (ContinuousMultilinearMap.norm_smulRight _ v)

/-- `main:lem:smoothing`: the vector-valued kernel integrand is continuous. -/
theorem continuous_periodicCutoffDerivKernel_smulRight {f : Torus n → F}
    (hf : Continuous f) (j : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun y ↦ (periodicCutoffDerivKernel j R x y).smulRight (f y)) :=
  (ContinuousMultilinearMap.smulRightL ℝ
    (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F).continuous₂.comp₂
      (continuous_periodicCutoffDerivKernel j R x) hf

private theorem iteratedFDeriv_periodicFourierMode_apply (j : ℕ) (k : Fin n → ℤ)
    (a : F × F) (x : EuclideanSpace ℝ (Fin n))
    (v : Fin j → EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (periodicLift (periodicFourierMode k a)) x v =
      iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).re) x v • a.1 -
      iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).im) x v • a.2 := by
  change iteratedFDeriv ℝ j (fun z ↦
    (periodicLift (UnitAddTorus.mFourier k) z).re • a.1 -
    (periodicLift (UnitAddTorus.mFourier k) z).im • a.2) x v = _
  rw [iteratedFDeriv_sub_fun_apply
    ((contDiff_re_character k j).contDiffAt.smul_const a.1)
    ((contDiff_im_character k j).contDiffAt.smul_const a.2),
    iteratedFDeriv_smul_const_apply (contDiff_re_character k j).contDiffAt,
    iteratedFDeriv_smul_const_apply (contDiff_im_character k j).contDiffAt]
  rfl

/-- `main:lem:smoothing`: the actual cutoff derivatives are integrals against
the derivative of its fixed scalar kernel. No kernel estimate is assumed. -/
theorem iteratedFDeriv_periodicCutoff_eq_integral {f : Torus n → F}
    (hf : Continuous f) (j : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (periodicLift (periodicCutoff R f)) x =
      ∫ y, (periodicCutoffDerivKernel j R x y).smulRight (f y) := by
  ext v
  rw [ContinuousMultilinearMap.integral_apply
    ((continuous_periodicCutoffDerivKernel_smulRight hf j R x
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change iteratedFDeriv ℝ j (fun z ↦ ∑ k ∈ periodicCutoffBox n R,
    periodicCutoffSymbol R k • periodicLift (periodicFourierMode k (periodicFourierCoeff f k)) z)
      x v = _
  rw [iteratedFDeriv_fun_sum_apply (fun k _ ↦
    (((isSmoothPeriodic_periodicFourierMode k (periodicFourierCoeff f k)).2.of_le
      (by simp : (j : WithTop ℕ∞) ≤ ∞)).contDiffAt.const_smul _))]
  simp only [sum_apply,
    iteratedFDeriv_const_smul_apply' (((isSmoothPeriodic_periodicFourierMode _ _).2.of_le
      (by simp : (j : WithTop ℕ∞) ≤ ∞)).contDiffAt),
    smul_apply, iteratedFDeriv_periodicFourierMode_apply,
    ContinuousMultilinearMap.smulRight_apply, periodicCutoffDerivKernel,
    sum_apply, smul_apply,
    sub_apply, Finset.sum_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    have hr : Integrable (fun y ↦ (UnitAddTorus.mFourier (-k) y).re • f y) :=
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi : Integrable (fun y ↦ (UnitAddTorus.mFourier (-k) y).im • f y) :=
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous).smul hf
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [smul_eq_mul, mul_comm (Complex.re _) _, mul_comm (Complex.im _) _,
      mul_smul, sub_smul]
    rw [integral_smul, integral_sub, integral_smul, integral_smul]
    · rfl
    · exact hr.smul (iteratedFDeriv ℝ j
        (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).re) x v)
    · exact hi.smul (iteratedFDeriv ℝ j
        (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).im) x v)
  · intro k _
    exact (by fun_prop : Continuous (fun y ↦
      (periodicCutoffSymbol R k •
        ((UnitAddTorus.mFourier (-k) y).re •
            iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).re) x v -
         (UnitAddTorus.mFourier (-k) y).im •
            iteratedFDeriv ℝ j (fun z ↦ (periodicLift (UnitAddTorus.mFourier k) z).im) x v)) • f y)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `main:eq:smoothing-low`: the pointwise derivative is controlled by the
L¹ mass of the actual scalar derivative kernel, for all complete real codomains. -/
theorem norm_iteratedFDeriv_periodicCutoff_le_kernel_mass {f : Torus n → F}
    (hf : Continuous f) {M : ℝ} (hbound : ∀ y, ‖f y‖ ≤ M)
    (j : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift (periodicCutoff R f)) x‖ ≤
      (∫ y, ‖periodicCutoffDerivKernel j R x y‖) * M := by
  rw [iteratedFDeriv_periodicCutoff_eq_integral hf]
  calc
    _ ≤ ∫ y, ‖periodicCutoffDerivKernel j R x y‖ * M := by
      apply norm_integral_le_of_norm_le
        ((integrable_norm_periodicCutoffDerivKernel j R x).mul_const M)
      exact Filter.Eventually.of_forall (fun y ↦ by
        rw [ContinuousMultilinearMap.norm_smulRight]
        exact mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    _ = _ := integral_mul_const M _

end JanetCartan
