module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Adjoint.Kernel
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.FourierAction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Realization

/-!
# Schwartz action of the literal cross-quantization adjoint

The bounded adjoint is `Li.adjoint.comp (1 - Ro.adjoint)`. The existing
identification producers realize these two adjoints as the original right
inner and left outer localizers. Fourier inversion and an absolutely
integrable Fubini argument give the conjugate-transposed kernel.
Consumer: the adjoint Sobolev extension for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph KernelLimits
open ResidualLocalization.IdentityDefect

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal Fourier action of `Ri (f - Lo f)` on Schwartz tests.
The complement is retained inside the amplitude; its noncompact frequency
support is controlled by Schwartz decay, not discarded
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjoint_fourier_action
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (hi : Continuous mi)
    (his : HasCompactSupport mi) (ho : Continuous mo) (hos : HasCompactSupport mo)
    (f g : SchwartzMap E (Fin r → ℂ))
    (hg : ∀ x, g x = leftLocalizer ρ mo f x) (ξ : E) :
    rightLocalizerFourierDensity ρ mi (f - g) ξ =
      ∫ η, crossQuantizationAdjointFourierKernel ρ mi mo ξ η •
        channelFourierTransform f η := by
  obtain ⟨B, hB⟩ := hos.exists_bound_of_continuous ho
  let a : E → ℂ := fun z ↦ (mi (z, ρ⁻¹ • ξ) : ℂ)
  have ha : Continuous a := Complex.continuous_ofReal.comp
    (hi.comp (continuous_id.prodMk continuous_const))
  have hca : HasCompactSupport a := by
    apply HasCompactSupport.intro (his.image continuous_fst)
    intro z hz
    have hm : mi (z, ρ⁻¹ • ξ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hz ⟨_, h, rfl⟩)
    simp [a, hm]
  let c : E × E → ℂ := fun p ↦ (1 - mo (p.1, ρ⁻¹ • p.2) : ℝ)
  have hc : Continuous c := Complex.continuous_ofReal.comp
    (continuous_const.sub (ho.comp
      (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹))))
  have hcb p : ‖c p‖ ≤ 1 + B := by
    change ‖((1 - mo (p.1, ρ⁻¹ • p.2) : ℝ) : ℂ)‖ ≤ 1 + B
    rw [Complex.norm_real]
    exact (norm_sub_le (1 : ℝ) (mo (p.1, ρ⁻¹ • p.2))).trans
      (by simpa only [norm_one] using add_le_add le_rfl (hB (p.1, ρ⁻¹ • p.2)))
  let F : E × E → Fin r → ℂ := fun p ↦
    (Complex.exp (Complex.I * (-(inner ℝ p.1 (ξ - p.2)) : ℝ)) *
      a p.1 * c p) • channelFourierTransform f p.2
  have hF : Continuous F := by
    have hp : Continuous (fun p : E × E ↦
      Complex.exp (Complex.I * (-(inner ℝ p.1 (ξ - p.2)) : ℝ))) := by fun_prop
    exact ((hp.mul (ha.comp continuous_fst)).mul hc).smul
      ((channelFourierTransform f).continuous.comp continuous_snd)
  have hint : Integrable F (volume.prod volume) := by
    apply (((ha.integrable_of_hasCompactSupport hca).norm.mul_prod
      (channelFourierTransform f).integrable.norm).const_mul (1 + B)).mono'
      hF.aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [F]
    simp only [norm_smul, norm_mul, mul_comm Complex.I,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ ‖a p.1‖ * (1 + B) * ‖channelFourierTransform f p.2‖ := by
        gcongr
        exact hcb p
      _ = _ := by ring
  have he z : (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) * a z) •
      (f - g) z = ∫ η, F (z, η) := by
    have hcomp := complementary_channelFourierIntegral ρ mo f z
      (ho.comp (continuous_const.prodMk (continuous_id.const_smul ρ⁻¹))) B
      (fun η ↦ hB (z, ρ⁻¹ • η))
    rw [sub_apply, hg z, ← hcomp, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [F, smul_smul]
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
          Complex.exp (Complex.I * (inner ℝ z η : ℂ))) * a z * c (z, η) := by
            dsimp only [c]
            ring
      _ = _ := by rw [hp]
  unfold rightLocalizerFourierDensity
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    (∫ z, (Complex.exp (Complex.I * (-(inner ℝ z ξ) : ℝ)) * a z) • (f - g) z) = _
  simp_rw [he]
  rw [integral_integral_swap hint, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [crossQuantizationAdjointFourierKernel_eq_integral]
  simp only [F, a, c, Complex.ofReal_mul, ← mul_assoc, integral_smul_const, smul_smul]
  congr 1
  push_cast
  rfl

/-- The actual bounded cross-product adjoint has a Schwartz representative
and the literal conjugate-transposed Fourier kernel. The action hypotheses
are precisely those produced by `exists_bounded_physicalLocalizers`; both
adjoint identifications are discharged here, without identifying left and
right quantizations (`app:ch_regular:eq:chain-tail`). -/
theorem bounded_crossQuantization_adjoint_schwartz_fourier_action
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (Li Ro : H →L[ℂ] H)
    (hLi : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hRo : ∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (f : SchwartzMap E (Fin r → ℂ)) :
    ∃ w : SchwartzMap E (Fin r → ℂ),
      ((1 - Ro).comp Li).adjoint
          ((LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2)
        =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (w x)) ∧
      ∀ ξ, channelFourierTransform w ξ =
        ∫ η, crossQuantizationAdjointFourierKernel ρ mi mo ξ η •
          channelFourierTransform f η := by
  have hLo := leftLocalizer_adjoint_ae_of_rightLocalizer hρ mo ho.continuous hos Ro hRo
  have hRi := rightLocalizer_adjoint_ae_of_leftLocalizer hρ mi hi.continuous his Li hLi
  let u := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2
  have hu := (LowBounds.FrequencyCutoff.toEuclideanSchwartz f).coeFn_toLp 2
  obtain ⟨g, hg, _⟩ := exists_leftLocalizer_schwartz hρ mo ho hos f
  obtain ⟨w, hw, hwF⟩ := exists_rightLocalizer_schwartz hρ mi hi his (f - g)
    ((f - g).smooth ⊤)
  have hint i : Integrable (fun y ↦ u y i) := by
    apply (f.integrable.eval i).congr
    filter_upwards [hu] with y hy
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v i) hy).symm
  have hL : Ro.adjoint u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (g x) := by
    refine (hLo u hint).trans (.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    rw [hg]
    unfold leftLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with η
    apply integral_congr_ae
    filter_upwards [hu] with y hy
    rw [show u y = WithLp.toLp 2 (f y) from hy]
  have hsub : u - Ro.adjoint u =ᵐ[volume] fun x ↦ WithLp.toLp 2 ((f - g) x) := by
    filter_upwards [Lp.coeFn_sub u (Ro.adjoint u), hu, hL] with x hx hf hl
    rw [hx, Pi.sub_apply, show u x = WithLp.toLp 2 (f x) from hf, hl]
    rfl
  refine ⟨w, ?_, fun ξ ↦ (hwF ξ).trans
    (crossQuantizationAdjoint_fourier_action ρ mi mo hi.continuous his
      ho.continuous hos f g hg ξ)⟩
  rw [ContinuousLinearMap.adjoint_comp, map_sub,
    ContinuousLinearMap.adjoint_one]
  change Li.adjoint (u - Ro.adjoint u) =ᵐ[volume] _
  refine (hRi _).trans (.of_forall fun x ↦ ?_)
  apply congrArg (WithLp.toLp 2)
  rw [hw]
  unfold rightLocalizer graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [hsub] with y hy
  rw [hy]

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
