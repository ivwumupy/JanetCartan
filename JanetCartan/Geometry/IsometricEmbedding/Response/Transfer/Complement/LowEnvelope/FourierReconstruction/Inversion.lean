module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.FourierDatum
/-!
# Physical inverse Fourier reconstruction of the low envelope

The envelope reconstruction used in `app:ch_response:thm:response-literal-transfer`,
including low-support L² data and exact cancellation of the Fourier normalization.
Passing this identity through the full forward and reverse graph integrals requires
the separate source/frequency Fubini argument.
-/

open MeasureTheory FourierTransform
open scoped ContDiff
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization
variable {n r : ℕ}
/-- Absolute integrability of physical inverse Fourier reconstruction,
consumed by the graph Fubini step in
`app:ch_response:thm:response-literal-transfer`. -/
theorem integrable_physical_inverse_integrand
    {H : Euclidean n → EuclideanSpace ℂ (Fin r)} (hH : Integrable H) (x : Euclidean n) :
    Integrable (fun θ ↦ phaseOscillation (fun z ↦ inner ℝ z θ) x • H θ) := by
  have hc : Continuous (fun θ : Euclidean n ↦ phaseOscillation (fun z ↦ inner ℝ z θ) x) := by
    unfold phaseOscillation
    fun_prop
  exact hH.bdd_smul 1 hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ ↦ (norm_phaseOscillation _ _).le))

/-- The ordinary inverse Fourier integral represents the inverse L²
transform almost everywhere. This supplies inversion for the low L² envelope
in `app:ch_response:thm:response-literal-transfer`. -/
theorem fourierInv_coeFn_ae_integral
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hf : Integrable (f : Euclidean n → EuclideanSpace ℂ (Fin r))) :
    (𝓕⁻ f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) =ᵐ[volume]
      𝓕⁻ (f : Euclidean n → EuclideanSpace ℂ (Fin r)) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ f)).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      ((innerSL ℝ).continuous₂.neg) hf).locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let s := hc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution (Euclidean n) (EuclideanSpace ℂ (Fin r)) ↦ T s)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  have hs := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.lsmul ℂ ℂ) (μ := volume) (ν := volume) (L := -innerₗ (Euclidean n))
    Real.continuous_fourierChar continuous_inner.neg s.integrable hf
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hd
  have hs' : (∫ x, (𝓕⁻ s) x • f x) =
      ∫ x, s x • 𝓕⁻ (f : Euclidean n → EuclideanSpace ℂ (Fin r)) x := by
    have hflip : (-innerₗ (Euclidean n)).flip = -innerₗ (Euclidean n) := by
      ext u v
      simp [real_inner_comm]
    rw [hflip] at hs
    simpa only [SchwartzMap.fourierInv_coe] using! hs
  simpa [s, Function.comp_def] using! hd.symm.trans hs'

/-- The physical inverse integral cancels the paper's Fourier
normalization exactly (`app:ch_response:thm:response-literal-transfer`).
Consequently graph reconstruction retains just the graph's outer `(2π)⁻ⁿ`. -/
theorem physical_inverse_integral_eq_fourierInv
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (x : Euclidean n) :
    (∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
      (((2 * Real.pi) ^ n : ℝ)⁻¹ • H ((2 * Real.pi)⁻¹ • θ))) = 𝓕⁻ H x := by
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have he : (∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x • H (a⁻¹ • θ)) =
      a ^ n • 𝓕⁻ H x := by
    have ht := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun θ : Euclidean n ↦ phaseOscillation (fun z ↦ inner ℝ z (a • θ)) x • H θ) ha.le
    simp only [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, finrank_euclideanSpace_fin] at ht
    rw [ht]
    congr 1
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with θ
    apply congrArg (fun c : ℂ ↦ c • H θ)
    simp only [phaseOscillation, inner_smul_right, a, real_inner_comm x θ]
  change (∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x • (a ^ n)⁻¹ • H (a⁻¹ • θ)) = _
  simp_rw [smul_comm (phaseOscillation _ _) ((a ^ n)⁻¹)]
  rw [integral_smul, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'), one_smul]

/-- Integrability of the paper-normalized physical Fourier datum implies
integrability in Mathlib's frequency coordinates, for the inversion step of
`app:ch_response:thm:response-literal-transfer`. -/
theorem integrable_fourier_of_integrable_paperL2
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hf : Integrable (paperL2FourierTransform f)) :
    Integrable (𝓕 f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume) := by
  have ha : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hi := (hf.comp_smul ha).smul ((2 * Real.pi : ℝ) ^ n)
  change Integrable (fun x ↦ ((2 * Real.pi : ℝ) ^ n) •
    paperL2FourierTransform f ((2 * Real.pi : ℝ) • x)) at hi
  simpa only [paperL2FourierTransform, smul_smul, inv_mul_cancel₀ ha,
    mul_inv_cancel₀ (pow_ne_zero _ ha), one_smul] using hi

/-- Physical Fourier inversion for an L² datum with integrable Fourier
transform (`app:ch_response:thm:response-literal-transfer`). No physical L¹
hypothesis or continuity of the datum is required. -/
theorem paperL2FourierTransform_inverse_ae
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    (hf : Integrable (paperL2FourierTransform f)) :
    (fun x ↦ ∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
      paperL2FourierTransform f θ) =ᵐ[volume] f := by
  have he := fourierInv_coeFn_ae_integral (𝓕 f)
    (integrable_fourier_of_integrable_paperL2 f hf)
  simp only [fourierInv_fourier_eq] at he
  filter_upwards [he] with x hx
  rw [hx]
  exact physical_inverse_integral_eq_fourierInv _ x

/-- Physical Fourier reconstruction of the low-support L² envelope
(`app:ch_response:thm:response-literal-transfer`). All integrals use Lebesgue
measure; the equality is almost everywhere in the physical source variable. -/
theorem paperL2FourierTransform_lowSupport_inverse_ae
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    (fun x ↦ ∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
      paperL2FourierTransform f θ) =ᵐ[volume] f :=
  paperL2FourierTransform_inverse_ae f (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1
/-- Reconstruction using the existing `paperFourierTransform` on L¹ ∩ L²,
with integrable Fourier datum (`app:ch_response:thm:response-literal-transfer`). -/
theorem paperFourierTransform_inverse_ae
    {f : Euclidean n → EuclideanSpace ℂ (Fin r)}
    (hf : Integrable f) (hf₂ : MemLp f 2 volume)
    (hF : Integrable (paperFourierTransform f)) :
    (fun x ↦ ∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
      paperFourierTransform f θ) =ᵐ[volume] f := by
  have hF' : paperL2FourierTransform (hf₂.toLp f) =ᵐ[volume]
      paperFourierTransform f := by
    refine (paperL2FourierTransform_eq_paperFourierTransform_ae (hf₂.toLp f)
      (hf.congr hf₂.coeFn_toLp.symm)).trans ?_
    apply Filter.Eventually.of_forall
    intro θ
    simp only [paperFourierTransform, physicalFourierIntegral_eq_fourier]
    rw [Real.fourier_congr_ae hf₂.coeFn_toLp]
  have hi := paperL2FourierTransform_inverse_ae (hf₂.toLp f) (hF.congr hF'.symm)
  filter_upwards [hi, hf₂.coeFn_toLp] with x hx hfx
  rw [← hfx, ← hx]
  apply integral_congr_ae
  filter_upwards [hF'] with θ hθ
  rw [hθ]

/-- Low-support reconstruction using the literal ordinary Fourier integral
on L¹ ∩ L² (`app:ch_response:thm:response-literal-transfer`). The separate
`paperL2FourierTransform_lowSupport_inverse_ae` handles general L² data. -/
theorem paperFourierTransform_lowSupport_inverse_ae
    {f : Euclidean n → EuclideanSpace ℂ (Fin r)}
    (hf : Integrable f) (hf₂ : MemLp f 2 volume) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperFourierTransform f θ = 0) :
    (fun x ↦ ∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
      paperFourierTransform f θ) =ᵐ[volume] f :=
  paperFourierTransform_inverse_ae hf hf₂ (paperFourierTransform_lowSupport_L1 hf hf₂ hΛ hs).1
end JanetCartan.ResponseTransfer.LowEnvelope
