module

public import JanetCartan.Analysis.Microlocal.Localization.GradedTranspose
public import JanetCartan.Analysis.Microlocal.Localization.Phase
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative integration by parts with compact support

For `app:ch_osc:prop:osc-source-shell`, compact support and local smoothness
justify every integration by parts. The final estimate uses the actual phase
coefficients, with their graded derivative bounds as an explicit input.
No coefficient derivative estimate or Fourier shell conclusion is assumed proved.
-/

@[expose] public noncomputable section

open scoped ContDiff
open MeasureTheory

namespace JanetCartan.Localization

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- `app:ch_osc:prop:osc-source-shell`: Local smoothness near the closed support gives global
smoothness of the zero extension. -/
theorem contDiff_of_contDiffOn_support_neighborhood {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hU.mem_nhds (hs hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

/-- `app:ch_osc:prop:osc-source-shell`: All transposed amplitudes have compact support. -/
theorem hasCompactSupport_iterate_transposeAmplitude (e : ι → E) (b : ι → E → ℂ) {a : E → ℂ}
    (ha : HasCompactSupport a) (q : ℕ) :
    HasCompactSupport ((transposeAmplitude e b)^[q] a) :=
  ha.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_iterate_transposeAmplitude_subset e b a q)

/-- `app:ch_osc:prop:osc-source-shell`: Global smoothness follows without extending the
coefficients smoothly outside the amplitude support. -/
theorem contDiff_iterate_transposeAmplitude {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (q : ℕ) :
    ContDiff ℝ ∞ ((transposeAmplitude e b)^[q] a) :=
  contDiff_of_contDiffOn_support_neighborhood hU (contDiffOn_iterate_transposeAmplitude hU e b a hb ha q)
    ((tsupport_iterate_transposeAmplitude_subset e b a q).trans hs)

/-- `app:ch_osc:prop:osc-source-shell`: The coefficient-amplitude product is globally smooth. -/
theorem contDiff_mul_of_support_neighborhood {U : Set E} (hU : IsOpen U)
    {b a : E → ℂ} (hb : ContDiffOn ℝ ∞ b U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) : ContDiff ℝ ∞ (fun x ↦ b x * a x) :=
  contDiff_of_contDiffOn_support_neighborhood hU (hb.mul ha) (tsupport_mul_subset_right.trans hs)

/-- `app:ch_osc:prop:osc-source-shell`: The actual reciprocal coefficients are smooth on the open
set where the gradient square is nonzero. -/
theorem contDiffOn_phaseCoefficient {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hg : ∀ x ∈ U, phaseGradientSquare e ψ x ≠ 0) (i : ι) :
    ContDiffOn ℝ ∞ (phaseCoefficient e ψ i) U := by
  have hd (j : ι) : ContDiffOn ℝ ∞ (fun x ↦ fderiv ℝ ψ x (e j)) U :=
    (hψ.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hs : ContDiffOn ℝ ∞ (phaseGradientSquare e ψ) U := by
    apply ContDiffOn.sum
    intro j _
    exact (hd j).pow 2
  have hn : ContDiffOn ℝ ∞ (fun x ↦ (fderiv ℝ ψ x (e i) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hd i)
  have hden : ContDiffOn ℝ ∞ (fun x ↦ Complex.I * (phaseGradientSquare e ψ x : ℂ)) U :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hs)
  change ContDiffOn ℝ ∞ (fun x ↦ (fderiv ℝ ψ x (e i) : ℂ) /
    (Complex.I * (phaseGradientSquare e ψ x : ℂ))) U
  simp only [div_eq_mul_inv]
  apply hn.mul (hden.inv _)
  intro x hx
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hg x hx))

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_osc:prop:osc-source-shell`: Compact support discharges all integrability and
boundary-term conditions in repeated transposition. -/
theorem integral_eq_iterate_transposeAmplitude_of_hasCompactSupport {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (f a : E → ℂ) (q : ℕ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (hf : ContDiffOn ℝ ∞ f U)
    (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    (hn : ∀ x ∈ tsupport a, ∑ i, b i x * fderiv ℝ f x (e i) = f x) :
    (∫ x, f x * a x ∂μ) = ∫ x, f x * ((transposeAmplitude e b)^[q] a) x ∂μ := by
  have hsmooth (k : ℕ) (i : ι) :
      ContDiff ℝ ∞ (fun x ↦ b i x * ((transposeAmplitude e b)^[k] a) x) :=
    contDiff_mul_of_support_neighborhood hU (hb i) (contDiffOn_iterate_transposeAmplitude hU e b a hb ha k)
      ((tsupport_iterate_transposeAmplitude_subset e b a k).trans hs)
  have hcompact (k : ℕ) (i : ι) :
      HasCompactSupport (fun x ↦ b i x * ((transposeAmplitude e b)^[k] a) x) :=
    (hasCompactSupport_iterate_transposeAmplitude e b hc k).mul_left
  have hsubset (k : ℕ) (i : ι) :
      tsupport (fun x ↦ b i x * ((transposeAmplitude e b)^[k] a) x) ⊆ U :=
    tsupport_mul_subset_right.trans
      ((tsupport_iterate_transposeAmplitude_subset e b a k).trans hs)
  apply integral_eq_integral_iterate_transposeAmplitude e b f a q
  · intro k _ x hx
    exact hn x (tsupport_iterate_transposeAmplitude_subset e b a k (subset_tsupport _ hx))
  · intro k _ i
    apply Continuous.integrable_of_hasCompactSupport
    · apply ContDiff.continuous (n := ∞) (𝕜 := ℝ)
      apply contDiff_of_contDiffOn_support_neighborhood hU
      · exact (((hsmooth k i).fderiv_right (m := ∞) (by simp)).contDiffOn.clm_apply
          contDiffOn_const).mul hf
      · exact tsupport_mul_subset_left.trans
          ((tsupport_fderiv_apply_subset ℝ (e i)).trans (hsubset k i))
    · exact ((hcompact k i).fderiv_apply ℝ (e i)).mul_right
  · intro k _ i
    apply Continuous.integrable_of_hasCompactSupport
    · apply ContDiff.continuous (n := ∞) (𝕜 := ℝ)
      apply contDiff_of_contDiffOn_support_neighborhood hU
      · exact (hsmooth k i).contDiffOn.mul
          ((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)
      · exact tsupport_mul_subset_left.trans (hsubset k i)
    · exact (hcompact k i).mul_right
  · intro k _ i
    exact (contDiff_of_contDiffOn_support_neighborhood hU ((hsmooth k i).contDiffOn.mul hf)
      (tsupport_mul_subset_left.trans (hsubset k i))).continuous.integrable_of_hasCompactSupport
      (hcompact k i).mul_right
  · intro k _ i x _
    exact (hsmooth k i).differentiable (by simp) x
  · intro k _ i x hx
    exact (hf.contDiffAt (hU.mem_nhds (hsubset k i hx))).differentiableAt (by simp)

/-- `app:ch_osc:prop:osc-source-shell`: A quantitative repeated integration-by-parts estimate,
with explicit coefficient and amplitude derivative profiles. -/
theorem norm_integral_le_transposeDerivativeConstant {U : Set E} (hU : IsOpen U)
    (e : ι → E) (b : ι → E → ℂ) (f a : E → ℂ) (q : ℕ)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (hf : ContDiffOn ℝ ∞ f U)
    (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    (hn : ∀ x ∈ tsupport a, ∑ i, b i x * fderiv ℝ f x (e i) = f x)
    (hu : ∀ x, ‖f x‖ ≤ 1) {B C : ℕ → ℝ} {A L R : ℝ}
    (hB : ∀ r, 0 ≤ B r) (hL : 0 ≤ L) (hR : 0 < R)
    (hbn : ∀ x ∈ tsupport a, ∀ i r, ‖iteratedFDeriv ℝ r (b i) x‖ ≤ B r * L ^ r / R)
    (han : ∀ x ∈ tsupport a, ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖∫ x, f x * a x ∂μ‖ ≤
      (transposeDerivativeConstant e B C q 0 * (A * (L / R) ^ q)) * μ.real (tsupport a) := by
  rw [integral_eq_iterate_transposeAmplitude_of_hasCompactSupport hU e b f a q hb hf ha hs hc hn]
  have hz (x : E) (hx : x ∉ tsupport a) :
      f x * ((transposeAmplitude e b)^[q] a) x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (tsupport_iterate_transposeAmplitude_subset e b a q h)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply norm_setIntegral_le_of_norm_le_const hc.measure_lt_top
  intro x hx
  have h := norm_iteratedFDeriv_iterate_transposeAmplitude_le_graded hU e b a hb ha
    (hs hx) hB hL hR (hbn x hx) (han x hx) q 0
  simp only [norm_iteratedFDeriv_zero, Nat.add_zero] at h
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)).trans
  simpa only [one_mul, div_pow, mul_div_assoc] using h

/-- `app:ch_osc:prop:osc-source-shell`: The quantitative scalar estimate for the actual phase
operator. The coefficient derivative profile is still an input. For the Fourier phase use `ψ =
fourierPhase φ ρ ξ`, `R = ρ + ‖ξ‖`, and include `Lᵇ` in `A`. -/
theorem norm_oscillatory_integral_le_of_coefficient_bounds {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (a : E → ℂ) (q : ℕ)
    (hψ : ContDiffOn ℝ ∞ ψ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    (hg : ∀ x ∈ U, phaseGradientSquare e ψ x ≠ 0)
    {B C : ℕ → ℝ} {A L R : ℝ}
    (hB : ∀ r, 0 ≤ B r) (hL : 0 ≤ L) (hR : 0 < R)
    (hbn : ∀ x ∈ tsupport a, ∀ i r,
      ‖iteratedFDeriv ℝ r (phaseCoefficient e ψ i) x‖ ≤ B r * L ^ r / R)
    (han : ∀ x ∈ tsupport a, ∀ r, ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖∫ x, phaseOscillation ψ x * a x ∂μ‖ ≤
      (transposeDerivativeConstant e B C q 0 * (A * (L / R) ^ q)) * μ.real (tsupport a) := by
  apply norm_integral_le_transposeDerivativeConstant hU e (phaseCoefficient e ψ) (phaseOscillation ψ) a q
    (contDiffOn_phaseCoefficient hU e ψ hψ hg) _ ha hs hc _ _ hB hL hR hbn han
  · exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn hψ).mul contDiffOn_const).cexp
  · intro x hx
    exact phaseCoefficient_normalizes e ψ
      ((hψ.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt (by simp)) (hg x (hs hx))
  · intro x
    exact (norm_phaseOscillation ψ x).le

end JanetCartan.Localization
