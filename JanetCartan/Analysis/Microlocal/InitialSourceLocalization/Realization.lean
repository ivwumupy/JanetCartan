module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FourierKernel
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerComposition
public import JanetCartan.Analysis.Microlocal.Localization.ComplexFubini

/-!
# The literal initial defect and its normalized Fourier density

The right quantization is the existing `rightLocalizer`, with precisely the
original source base and `(2*pi)^(-n)` factor. Compact smooth source data and
the published right-localizer realization give a Schwartz representative of
their difference. Its Fourier density is the complementary kernel estimated
from graph geometry in `FourierKernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory FourierTransform Filter
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph FiniteChain.Graph.KernelLimits JanetCartan.Localization
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect

variable {n r : ℕ}
local notation "E" => Euclidean n

/-- The source minus its SAME right proof localizer has an actual Schwartz
representative. Its normalized physical Fourier transform is exactly the
single complementary-amplitude kernel; the identity contribution and
Fourier normalization are retained (`app:ch_regular:eq:source-tail`). -/
theorem exists_initialSource_defect_schwartz
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → Fin r → ℂ) {U : Set E} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∃ g : SchwartzMap E (Fin r → ℂ),
      (∀ x, g x = phaseOscillation (fun y ↦ ρ * φ y) x • a x -
        rightLocalizer ρ m (fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y) x) ∧
      ∀ ξ, channelFourierTransform g ξ = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        complementarySourceFourierKernel m φ a ρ ξ := by
  let f : E → Fin r → ℂ := fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y
  have hfU : ContDiffOn ℝ ∞ f U :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.const_smul ρ)).mul contDiffOn_const).cexp.smul ha
  have hf : ContDiff ℝ ∞ f := contDiff_of_contDiffOn_support_neighborhood hU hfU
    ((tsupport_smul_subset_right _ _).trans hs)
  have hfc : HasCompactSupport f :=
    hc.smul_left (f := phaseOscillation (fun z ↦ ρ * φ z))
  let u : SchwartzMap E (Fin r → ℂ) := hfc.toSchwartzMap hf
  obtain ⟨v, hv, hvF⟩ := exists_rightLocalizer_schwartz hρ m hm hmc f hf
  refine ⟨u - v, fun x ↦ ?_, fun ξ ↦ ?_⟩
  · change f x - v x = _
    rw [hv]
  · have hsub : channelFourierTransform (u - v) ξ =
        channelFourierTransform u ξ - channelFourierTransform v ξ := by
      change ((2 * Real.pi) ^ n : ℝ)⁻¹ •
        (𝓕 (u - v)) ((2 * Real.pi)⁻¹ • ξ) =
        ((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 u) ((2 * Real.pi)⁻¹ • ξ) -
        ((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 v) ((2 * Real.pi)⁻¹ • ξ)
      have hF : 𝓕 (u - v) = 𝓕 u - 𝓕 v :=
        (fourierCLM ℂ (SchwartzMap E (Fin r → ℂ))).map_sub u v
      rw [hF, sub_apply, smul_sub]
    rw [hsub, hvF, channelFourierTransform_eq_integral]
    have hec : Continuous (fun y : E ↦ Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_id.inner continuous_const).neg)))
    have hmξ : Continuous (fun y : E ↦ (m (y, ρ⁻¹ • ξ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hm.continuous.comp (continuous_id.prodMk continuous_const))
    have hi₁ : Integrable (fun y : E ↦
        Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) • f y) :=
      (hec.smul hf.continuous).integrable_of_hasCompactSupport
        (hfc.smul_left (f := fun y ↦ Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ))))
    have hi₂ : Integrable (fun y : E ↦
        (Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) *
          (m (y, ρ⁻¹ • ξ) : ℂ)) • f y) :=
      ((hec.mul hmξ).smul hf.continuous).integrable_of_hasCompactSupport
        (hfc.smul_left (f := fun y ↦ Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) *
          (m (y, ρ⁻¹ • ξ) : ℂ)))
    change ((2 * Real.pi) ^ n : ℂ)⁻¹ • (∫ y,
        Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) • f y) -
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (∫ y,
        (Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) *
          (m (y, ρ⁻¹ • ξ) : ℂ)) • f y) = _
    rw [← smul_sub, ← integral_sub hi₁ hi₂]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    have he : Complex.exp (Complex.I * (-(inner ℝ y ξ) : ℝ)) =
        phaseOscillation (fun z ↦ -(InnerProductSpace.toDual ℝ E ξ) z) y := by
      simp [phaseOscillation, InnerProductSpace.toDual_apply_apply, real_inner_comm,
        mul_comm]
    dsimp only [f]
    rw [he, phaseOscillation_fourierPhase]
    simp only [complementarySourceAmplitude, smul_smul, ← sub_smul]
    congr 1
    ring

end JanetCartan.InitialSourceLocalization
