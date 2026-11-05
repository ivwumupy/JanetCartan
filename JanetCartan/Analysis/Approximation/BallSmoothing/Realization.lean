module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Geometry
public import JanetCartan.Analysis.Approximation.BallSmoothing.KernelBounds
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Fixed-kernel realization of the literal ball average

For `app:ch_regular_base:lem:ball-extension`, extension by zero is used only
to justify global convolution calculus. On the entire active output collar
every sample is inside the original ball, so the resulting function is
identically the manuscript's radial average. Rescaling the input rather than
the kernel leaves one fixed `L¹` kernel derivative budget and the exact
per-derivative factor at most `R`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ContDiff Convolution

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The zero extension of the original closed-ball values, used only in
the convolution proof of `app:ch_regular_base:eq:ball-extension-sobolev`. -/
def inputExtension (f : E → F) : E → F := (closedBall (0 : E) 1).indicator f

omit [NormedSpace ℝ F] in
/-- Continuous closed-ball data give an integrable zero extension;
no exterior values or exterior regularity are used
(`app:ch_regular_base:lem:ball-extension`). -/
theorem integrable_inputExtension {f : E → F}
    (hf : ContinuousOn f (closedBall (0 : E) 1)) : Integrable (inputExtension f) :=
  (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (hf.integrableOn_compact (isCompact_closedBall _ _))

omit [NormedSpace ℝ F] in
/-- The zero extension retains exactly the source's uniform bound
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem norm_inputExtension_le {f : E → F} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ closedBall (0 : E) 1, ‖f x‖ ≤ M) (x : E) :
    ‖inputExtension f x‖ ≤ M := by
  by_cases hx : x ∈ closedBall (0 : E) 1
  · simpa [inputExtension, hx] using hf x hx
  · simpa [inputExtension, hx] using hM

/-- The input rescaling used with the single fixed smoothing kernel
(`app:ch_regular_base:eq:extension-radial-formula`). -/
def reflectedInput (R : ℝ) (j : ℕ) (f : E → F) (z : E) : F :=
  inputExtension f ((-(j : ℝ) / R) • z)

omit [NormedSpace ℝ F] in
/-- Integrability survives the nonzero input rescaling
(`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem integrable_reflectedInput {R : ℝ} (hR : R ≠ 0) {j : ℕ} (hj : j ≠ 0)
    {f : E → F} (hf : ContinuousOn f (closedBall (0 : E) 1)) :
    Integrable (reflectedInput R j f) := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  exact (integrable_inputExtension hf).comp_smul (div_ne_zero (neg_ne_zero.mpr hj') hR)

/-- Globally smooth convolution representative of the literal inward
average; equality on the active collar is proved below
(`app:ch_regular_base:eq:extension-radial-formula`). -/
def regularizedAverage (ρ : E → ℝ) (R : ℝ) (j : ℕ) (f : E → F) (x : E) : F :=
  (ρ ⋆[lsmul ℝ ℝ] reflectedInput R j f) ((1 - R / (j : ℝ)) • x)

/-- The original average and its global convolution representative agree
on the whole permitted collar. This is an identity of the actual integral
formula, not an assumption about a new smoother
(`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem radialAverage_eq_regularizedAverage {R : ℝ} (hR : 0 < R)
    {j : ℕ} (hj : 1 ≤ j) (hjR : (j : ℝ) ≤ R / 2)
    {ρ : E → ℝ} (hρ : tsupport ρ ⊆ ball (0 : E) (1 / 4))
    (f : E → F) {x : E} (hx : ‖x‖ ≤ 1 + 1 / (2 * R)) :
    radialAverage ρ R j f x = regularizedAverage ρ R j f x := by
  unfold radialAverage regularizedAverage convolution
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [lsmul_apply, reflectedInput]
  by_cases hy : ρ y = 0
  · simp [hy]
  · have hys : y ∈ tsupport ρ := subset_tsupport _ (by exact hy)
    have hp := radialPoint_mem_ball hR hj hjR hx (mem_ball_zero_iff.mp (hρ hys)).le
    rw [← radialPoint_eq_reflected hR.ne' (by omega : j ≠ 0)]
    simp only [inputExtension, indicator_of_mem (ball_subset_closedBall hp)]

/-- The fixed-kernel representative is smooth at all output orders using
only continuity of the input on the original closed ball
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem contDiff_regularizedAverage {R : ℝ} (hR : R ≠ 0) {j : ℕ} (hj : j ≠ 0)
    {ρ : E → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    {f : E → F} (hf : ContinuousOn f (closedBall (0 : E) 1)) :
    ContDiff ℝ ∞ (regularizedAverage ρ R j f) := by
  exact (hc.contDiff_convolution_left (lsmul ℝ ℝ) hρ
    (integrable_reflectedInput hR hj hf).locallyIntegrable).comp
      (contDiff_id.const_smul (1 - R / (j : ℝ)))

/-- Sharp all-order derivative bound for each actual inward averaging
term. The input enters only through its original closed-ball `C⁰` bound
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem norm_iteratedFDeriv_regularizedAverage_le {R : ℝ} (hR : 1 ≤ R)
    {j : ℕ} (hj : 1 ≤ j) {ρ : E → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ ∞ ρ) {f : E → F} (hf : ContinuousOn f (closedBall (0 : E) 1))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y ∈ closedBall (0 : E) 1, ‖f y‖ ≤ M)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (regularizedAverage ρ R j f) x‖ ≤
      (∫ y, ‖iteratedFDeriv ℝ r ρ y‖) * R ^ r * M := by
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have hj0 : j ≠ 0 := by omega
  have hs := (integrable_reflectedInput hR0 hj0 hf).locallyIntegrable
  have hconv : ContDiff ℝ ∞ (ρ ⋆[lsmul ℝ ℝ] reflectedInput R j f) :=
    hc.contDiff_convolution_left _ hρ hs
  have hb (z : E) : ‖iteratedFDeriv ℝ r (ρ ⋆[lsmul ℝ ℝ] reflectedInput R j f) z‖ ≤
      (∫ y, ‖iteratedFDeriv ℝ r ρ y‖) * M := by
    apply (norm_iteratedFDeriv_convolution_le_kernel r (lsmul ℝ ℝ) hc hρ hs hM
      (fun w ↦ norm_inputExtension_le hM hbound _) z).trans
    apply mul_le_mul_of_nonneg_right _ hM
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (opNorm_lsmul_le : ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ ≤ 1)
      (integral_nonneg fun y ↦ norm_nonneg (iteratedFDeriv ℝ r ρ y))
  unfold regularizedAverage
  rw [congrFun (iteratedFDeriv_comp_const_smul (1 - R / (j : ℝ))
    (hconv.of_le (by simp))) x, norm_smul, norm_pow, Real.norm_eq_abs]
  calc
    _ ≤ |1 - R / (j : ℝ)| ^ r * ((∫ y, ‖iteratedFDeriv ℝ r ρ y‖) * M) :=
      mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (abs_nonneg _) _)
    _ ≤ R ^ r * ((∫ y, ‖iteratedFDeriv ℝ r ρ y‖) * M) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (abs_affineFrequency_le hR hj) r)
        (mul_nonneg (integral_nonneg fun y ↦ norm_nonneg _) hM)
    _ = _ := by ring

/-- Output multiplication identifies the literal finite radial formula with
the same finite combination of globally smooth representatives. The physical
cutoff's collar certificate is its only geometric input
(`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem radialSmoothing_eq_regularized {R : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hR : (2 * m : ℝ) ≤ R) (χ : E → ℝ)
    (hχ : ∀ x, χ x ≠ 0 → ‖x‖ ≤ 1 + 1 / (2 * R))
    (a : ℕ → ℝ) {ρ : E → ℝ} (hρ : tsupport ρ ⊆ ball (0 : E) (1 / 4))
    (f : E → F) :
    radialSmoothing χ a ρ R m f = fun x ↦
      χ x • ∑ j ∈ Finset.Icc 1 m, a j • regularizedAverage ρ R j f x := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : 0 < R := by linarith
  funext x
  by_cases hx : χ x = 0
  · simp [radialSmoothing, hx]
  · unfold radialSmoothing radialCombination
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
    have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
    have hjR : (j : ℝ) ≤ R / 2 := by linarith
    rw [radialAverage_eq_regularizedAverage hR0 hj1 hjR hρ f (hχ x hx)]

end JanetCartan.BallSmoothing
