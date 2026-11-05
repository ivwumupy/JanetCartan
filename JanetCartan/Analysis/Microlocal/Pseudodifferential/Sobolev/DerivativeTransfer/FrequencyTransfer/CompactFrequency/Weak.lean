module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.CompactFrequency.Kernel

/-!
# Weak output derivatives at compact frequency

Compact physical support supplies every integrability premise in Fubini and
integration by parts for `app:ch_regular_base:eq:fio-input`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem compactFrequencyKernel_left_support
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (ρ : ℝ) (y : E) :
    HasCompactSupport (fun x ↦ compactFrequencyAmplitudeKernel b ρ x y) := by
  have h := hasCompactSupport_compactFrequencyAmplitudeKernel hs ρ
  apply HasCompactSupport.of_support_subset_isCompact (h.image continuous_fst)
  intro x hx
  exact ⟨(x, y), subset_tsupport (Function.uncurry (compactFrequencyAmplitudeKernel b ρ)) hx, rfl⟩

/-- `app:ch_regular_base:eq:fio-input`: the compact physical kernel gives joint
absolute integrability of its pairing with any two continuous functions. -/
theorem integrable_compactFrequencyAmplitudeKernel_pairing
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : Continuous (Function.uncurry b)) {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (ρ : ℝ)
    {f u : E → ℂ} (hf : Continuous f) (hu : Continuous u) :
    Integrable (fun p : E × E ↦ f p.1 *
      compactFrequencyAmplitudeKernel b ρ p.1 p.2 * u p.2) :=
  (((hf.comp continuous_fst).mul
    (continuous_compactFrequencyAmplitudeKernel hb ρ)).mul
      (hu.comp continuous_snd)).integrable_of_hasCompactSupport
        (hasCompactSupport_compactFrequencyAmplitudeKernel hs ρ).mul_left.mul_right

/-- `app:ch_regular_base:eq:fio-input`: the literal compact-frequency operator
has weak coordinate derivative given by the full output derivative amplitude.
Fubini and integration by parts are justified by the physical support. -/
theorem compactFrequencyAmplitudeKernel_weak_outputDerivative
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) {R : ℝ}
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (ρ : ℝ) (i : Fin d) {u : E → ℂ} (hu : Continuous u) (φ : 𝓢(E, ℂ)) :
    (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) *
      (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y)) =
      -(∫ x, φ x * (∫ y,
        compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y * u y)) := by
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdφ : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    ((φ.smooth ⊤).continuous_fderiv (by simp)).clm_apply continuous_const
  have hbd := contDiff_uncurry_outputDerivativeAmplitude hb i
  have hsd := supportedInCenteredBox_outputDerivativeAmplitude b R hs i
  have hib := integrable_compactFrequencyAmplitudeKernel_pairing hb.continuous hs ρ hdφ hu
  have hid := integrable_compactFrequencyAmplitudeKernel_pairing hbd.continuous hsd ρ
    φ.continuous hu
  have hparts (y : E) :
      (∫ x, fderiv ℝ φ x v * compactFrequencyAmplitudeKernel b ρ x y) =
        -(∫ x, φ x * compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y) := by
    have hk := contDiff_compactFrequencyAmplitudeKernel_left hb ρ y
    have hks := compactFrequencyKernel_left_support hs ρ y
    have hdk := (hk.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((hdk.mul φ.continuous).integrable_of_hasCompactSupport
        (hks.fderiv_apply ℝ v).mul_right)
      ((hk.continuous.mul hdφ).integrable_of_hasCompactSupport hks.mul_right)
      ((hk.continuous.mul φ.continuous).integrable_of_hasCompactSupport hks.mul_right)
      (fun x _ ↦ hk.differentiable (by simp) x)
      (fun x _ ↦ φ.differentiable x)
    simpa only [v, fderiv_compactFrequencyAmplitudeKernel_left hb, mul_comm] using h
  calc
    _ = ∫ x, ∫ y, (fderiv ℝ φ x v * compactFrequencyAmplitudeKernel b ρ x y) * u y := by
      simp only [← integral_const_mul, mul_assoc, v]
    _ = ∫ y, ∫ x, (fderiv ℝ φ x v * compactFrequencyAmplitudeKernel b ρ x y) * u y :=
      integral_integral_swap hib
    _ = -(∫ y, ∫ x, (φ x *
        compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y) * u y) := by
      simp_rw [integral_mul_const, hparts, neg_mul, integral_neg]
    _ = -(∫ x, ∫ y, (φ x *
        compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y) * u y) := by
      exact congrArg Neg.neg (integral_integral_swap hid).symm
    _ = _ := by simp only [← integral_const_mul, mul_assoc]

end JanetCartan.Pseudodifferential
