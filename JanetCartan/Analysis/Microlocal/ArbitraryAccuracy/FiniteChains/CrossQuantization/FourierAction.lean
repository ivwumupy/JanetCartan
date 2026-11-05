module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.FourierKernel

/-!
# Test action of the cross-quantized product

The original left localizer maps Schwartz tests to smooth compactly
supported fields. Fourier transformation of `(1-Ro) Li` then gives the
two-frequency kernel from `FourierKernel`, using Fubini on the original
compact symbol carrier. Consumer: the all-L² extension of the intermediate
cross estimate in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph KernelLimits
open ResidualLocalization.IdentityDefect
open FiniteChain.Retarded.KernelDecay

variable {n r : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The same left-quantized input is smooth and compact on Schwartz tests.
This supplies integrability for the actual subsequent right localizer,
without requiring any regularity of the eventual L² datum
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_leftLocalizer_schwartz {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (f : SchwartzMap E (Fin r → ℂ)) :
    ∃ g : SchwartzMap E (Fin r → ℂ),
      (∀ x, g x = leftLocalizer ρ mi f x) ∧ HasCompactSupport (g : E → Fin r → ℂ) := by
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (inner ℝ p.1 p.2 : ℂ)) *
      (mi (p.1, ρ⁻¹ • p.2) : ℂ)) • channelFourierTransform f p.2
  have hp : ContDiff ℝ ∞ (fun p : E × E ↦ inner ℝ p.1 p.2) :=
    contDiff_fst.inner ℝ contDiff_snd
  have hF : ContDiff ℝ ∞ F :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp.mul
      (Complex.ofRealCLM.contDiff.comp
        (hi.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ⁻¹))))).smul
      ((channelFourierTransform f).smooth ⊤ |>.comp contDiff_snd)
  have hs x η (hη : η ∉ (fun ξ : E ↦ ρ • ξ) '' (Prod.snd '' tsupport mi)) :
      F (x, η) = 0 := by
    have hm : mi (x, ρ⁻¹ • η) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hη ⟨ρ⁻¹ • η, ⟨(x, ρ⁻¹ • η), h, rfl⟩, by simp [smul_smul, hρ]⟩
    simp [F, hm]
  have hsm : ContDiff ℝ ∞ (leftLocalizer ρ mi f) := by
    change ContDiff ℝ ∞ (fun x ↦ leftLocalizer ρ mi f x)
    simp_rw [leftLocalizer_eq_channelFourierIntegral]
    exact contDiff_integral_commonCarrier hF
      ((his.image continuous_snd).image (continuous_id.const_smul ρ)) hs
  have hc : HasCompactSupport (leftLocalizer ρ mi f) := by
    apply HasCompactSupport.intro (his.image continuous_fst)
    intro x hx
    have hm η : mi (x, ρ⁻¹ • η) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx ⟨(x, ρ⁻¹ • η), h, rfl⟩)
    simp [leftLocalizer_eq_channelFourierIntegral, hm]
  exact ⟨hc.toSchwartzMap hsm, fun _ ↦ rfl, hc⟩

/-- The Fourier transform of the actual cross product on tests. The
intermediate `g` is produced by `exists_leftLocalizer_schwartz` for the SAME
input symbol. Compact joint support justifies Fubini; the complementary
factor is kept inside the amplitude (`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantization_fourier_action {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : Continuous mi) (his : HasCompactSupport mi)
    (ho : Continuous mo) (f g : SchwartzMap E (Fin r → ℂ))
    (hg : ∀ x, g x = leftLocalizer ρ mi f x)
    (hgc : HasCompactSupport (g : E → Fin r → ℂ)) (ξ : E) :
    channelFourierTransform g ξ - rightLocalizerFourierDensity ρ mo g ξ =
      ∫ η, crossQuantizationFourierKernel ρ mi mo ξ η • channelFourierTransform f η := by
  let a : E × E → ℂ := fun p ↦ (mi (p.1, ρ⁻¹ • p.2) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (hi.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
  have hca : HasCompactSupport a := by
    apply HasCompactSupport.intro
      (his.image (continuous_fst.prodMk (continuous_snd.const_smul ρ)))
    intro p hp
    have hz : mi (p.1, ρ⁻¹ • p.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hp ⟨(p.1, ρ⁻¹ • p.2), h, by simp [smul_smul, hρ]⟩
    simp [a, hz]
  let c : E → ℂ := fun z ↦ (1 - mo (z, ρ⁻¹ • ξ) : ℝ)
  have hc : Continuous c := Complex.continuous_ofReal.comp
    (continuous_const.sub (ho.comp (continuous_id.prodMk continuous_const)))
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (-(inner ℝ p.1 (ξ - p.2)) : ℝ)) * c p.1 * a p) •
      channelFourierTransform f p.2
  have hF : Continuous F := by
    have hp : Continuous (fun p : E × E ↦
        Complex.exp (Complex.I * (-(inner ℝ p.1 (ξ - p.2)) : ℝ))) := by fun_prop
    exact ((hp.mul (hc.comp continuous_fst)).mul ha).smul
      ((channelFourierTransform f).continuous.comp continuous_snd)
  have hcF : HasCompactSupport F := hca.mul_left.smul_right
  have hint : Integrable F (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hF.integrable_of_hasCompactSupport hcF
  have he z : (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) * c z) • g z =
      ∫ η, F (z, η) := by
    rw [hg z, leftLocalizer_eq_channelFourierIntegral, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [F, a, smul_smul]
    congr 1
    have hp : Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) *
        Complex.exp (Complex.I * (inner ℝ z η : ℂ)) =
        Complex.exp (Complex.I * (-(inner ℝ z (ξ - η)) : ℝ)) := by
      rw [← Complex.exp_add, inner_sub_right]
      congr 1
      push_cast
      ring
    calc
      _ = (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) *
          Complex.exp (Complex.I * (inner ℝ z η : ℂ))) * c z *
            (mi (z, ρ⁻¹ • η) : ℂ) := by ring
      _ = _ := by rw [hp]
  have h0 : Integrable (fun z ↦
      Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) • g z) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous (fun z : E ↦
        Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)))).smul g.continuous
    · exact hgc.smul_left (f := fun z : E ↦
        Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)))
  have h1 : Integrable (fun z ↦
      (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) *
        (mo (z, ρ⁻¹ • ξ) : ℂ)) • g z) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((by fun_prop : Continuous (fun z : E ↦
        Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)))).mul
          (Complex.continuous_ofReal.comp
            (ho.comp (continuous_id.prodMk continuous_const)))).smul g.continuous
    · exact hgc.smul_left (f := fun z : E ↦
        Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) * (mo (z, ρ⁻¹ • ξ) : ℂ))
  rw [channelFourierTransform_eq_integral, rightLocalizerFourierDensity,
    ← smul_sub, ← integral_sub h0 h1]
  have hsub : (fun z ↦ Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) • g z -
      (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) *
        (mo (z, ρ⁻¹ • ξ) : ℂ)) • g z) =
      fun z ↦ (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) * c z) • g z := by
    funext z
    simp only [c, Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one, sub_smul]
  rw [hsub]
  simp_rw [he]
  rw [integral_integral_swap hint, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [F, a, c, crossQuantizationFourierKernel, Complex.ofReal_mul,
    ← mul_assoc, integral_smul_const, smul_smul]
  congr 1
  push_cast
  rfl

/-- The literal bounded cross product has the proved Fourier kernel on
every Schwartz test. Both realization premises are supplied by
`exists_bounded_physicalLocalizers`; no equality between left and right
quantization is used. This identifies the actual operator to which the
uniform kernel estimate must be extended (`app:ch_regular:eq:chain-tail`). -/
theorem bounded_crossQuantization_schwartz_fourier_action {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (Li Ro : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E))
    (hLi : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hRo : ∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (f : SchwartzMap E (Fin r → ℂ)) :
    ∃ w : SchwartzMap E (Fin r → ℂ),
      (1 - Ro) (Li ((LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2))
        =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (w x)) ∧
      ∀ ξ, channelFourierTransform w ξ =
        ∫ η, crossQuantizationFourierKernel ρ mi mo ξ η • channelFourierTransform f η := by
  let u := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2
  have hu := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).coeFn_toLp 2
  obtain ⟨g, hg, hgc⟩ := exists_leftLocalizer_schwartz hρ mi hi his f
  obtain ⟨h, hh, hhF⟩ := exists_rightLocalizer_schwartz hρ mo ho hos g (g.smooth ⊤)
  have hint i : Integrable (fun y ↦ u y i) := by
    apply (f.integrable.eval i).congr
    filter_upwards [hu] with y hy
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v i) hy).symm
  have hL : Li u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (g x) := by
    refine (hLi u hint).trans (.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    rw [hg]
    unfold leftLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with η
    apply integral_congr_ae
    filter_upwards [hu] with y hy
    rw [show u y = WithLp.toLp 2 (f y) from hy]
  have hR : Ro (Li u) =ᵐ[volume] fun x ↦ WithLp.toLp 2 (h x) := by
    refine (hRo (Li u)).trans (.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    rw [hh]
    unfold rightLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with η
    apply integral_congr_ae
    filter_upwards [hL] with y hy
    rw [hy]
  refine ⟨g - h, ?_, ?_⟩
  · change Li u - Ro (Li u) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_sub (Li u) (Ro (Li u)), hL, hR] with x hx hl hr
    rw [hx, Pi.sub_apply, hl, hr]
    rfl
  · intro ξ
    have hsub : channelFourierTransform (g - h) =
        channelFourierTransform g - channelFourierTransform h := by
      have hfsub : 𝓕 (g - h) = 𝓕 g - 𝓕 h :=
        (fourierCLM ℂ (SchwartzMap E (Fin r → ℂ))).map_sub g h
      simp only [channelFourierTransform, hfsub, map_sub, smul_sub]
    rw [hsub, sub_apply, hhF]
    exact crossQuantization_fourier_action hρ mi mo hi.continuous his ho.continuous f g hg hgc ξ

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
