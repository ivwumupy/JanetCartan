module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerJets.Frequency
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Output derivatives of the same-localizer identity kernel

Compact frequency support permits differentiation of the original kernel.
Translation and scaling identify its derivatives with the exact graph
output-symbol jet, retaining `1-mo` and the physical Fourier convention.
Consumer: the principal identity leakage in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph KernelEstimates
open FiniteChain.Retarded.KernelDecay
variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The rescaled integral is exactly the original physical identity kernel;
no source or output term is omitted (`app:ch_regular:eq:chain-tail`). -/
theorem identityLeakageScalarKernel_eq_normalizedIntegral {ρ : ℝ} (hρ : 0 < ρ)
    (mi mo : LocalizerSymbol n) (x y : E) :
    identityLeakageScalarKernel ρ mi mo x y =
      ((ρ / (2 * Real.pi)) ^ n : ℝ) • ∫ η,
        Complex.exp ((ρ * inner ℝ (x - y) η : ℝ) * Complex.I) *
          (1 - (mo (x, η) : ℂ)) * (mi (y, η) : ℂ) := by
  rw [identityLeakageScalarKernel_eq_fourier hρ, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  have hp : -2 * Real.pi * inner ℝ η (-(ρ / (2 * Real.pi)) • (x - y)) =
      ρ * inner ℝ (x - y) η := by
    rw [inner_smul_right, real_inner_comm η (x - y)]
    field_simp
  simp only [hp, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, mul_assoc]

/-- Joint smoothness of the full identity kernel is derived from the compact
frequency projection of the original right mask (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_identityLeakageScalarKernel {ρ : ℝ} (hρ : 0 < ρ)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) :
    ContDiff ℝ ∞ (fun p : E × E ↦ identityLeakageScalarKernel ρ mi mo p.1 p.2) := by
  let f : (E × E) × E → ℂ := fun p ↦
    Complex.exp ((ρ * inner ℝ (p.1.1 - p.1.2) p.2 : ℝ) * Complex.I) *
      (1 - (mo (p.1.1, p.2) : ℂ)) * (mi (p.1.2, p.2) : ℂ)
  have hf : ContDiff ℝ ∞ f :=
    ((Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
        ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd))).mul
          contDiff_const)).mul
      (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (ho.comp (contDiff_fst.fst.prodMk contDiff_snd))))).mul
      (Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_fst.snd.prodMk contDiff_snd)))
  have hs p η (hη : η ∉ Prod.snd '' tsupport mi) : f (p, η) = 0 := by
    have hz : mi (p.2, η) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hη ⟨(p.2, η), h, rfl⟩)
    simp [f, hz]
  simp_rw [identityLeakageScalarKernel_eq_normalizedIntegral hρ]
  exact (contDiff_integral_commonCarrier hf (his.image continuous_snd) hs).const_smul _

private theorem identityLeakage_integrand_outputJet {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (ho : ContDiff ℝ ∞ mo)
    (x y η : E) (j : ℕ) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun z : E ↦
      Complex.exp ((ρ * inner ℝ (z - y) η : ℝ) * Complex.I) *
        (1 - (mo (z, η) : ℂ)) * (mi (y, η) : ℂ)) x v =
      ρ ^ j • (Complex.exp ((ρ * inner ℝ (x - y) η : ℝ) * Complex.I) *
        identityLeakageJetAmplitude ρ mi mo x y j v η) := by
  let g : E → ℂ := fun t ↦ outputJointWave (t, η) *
    (1 - (mo (x + ρ⁻¹ • t, η) : ℂ))
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_outputJointWave.comp (contDiff_id.prodMk contDiff_const)).mul
      (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (ho.comp ((contDiff_const.add (contDiff_id.const_smul ρ⁻¹)).prodMk contDiff_const))))
  let c := Complex.exp ((ρ * inner ℝ (x - y) η : ℝ) * Complex.I) * (mi (y, η) : ℂ)
  have he : (fun t : E ↦
      Complex.exp ((ρ * inner ℝ (x + t - y) η : ℝ) * Complex.I) *
        (1 - (mo (x + t, η) : ℂ)) * (mi (y, η) : ℂ)) =
      fun t ↦ c • g (ρ • t) := by
    funext t
    dsimp only [c, g, outputJointWave]
    rw [inv_smul_smul₀ hρ, real_inner_smul_left,
      show x + t - y = (x - y) + t by abel, inner_add_left]
    push_cast
    rw [mul_add, add_mul, Complex.exp_add]
    simp only [smul_eq_mul]
    ring
  have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun z : E ↦ Complex.exp ((ρ * inner ℝ (z - y) η : ℝ) * Complex.I) *
      (1 - (mo (z, η) : ℂ)) * (mi (y, η) : ℂ)) j x 0
  have hgs : ContDiff ℝ ∞ (fun t : E ↦ g (ρ • t)) :=
    hg.comp (contDiff_id.const_smul ρ)
  rw [add_zero, he, iteratedFDeriv_const_smul_apply'
    (hgs.contDiffAt.of_le (by simp)),
    iteratedFDeriv_comp_const_smul ρ (hg.of_le (by simp))] at ht
  simp only [smul_zero] at ht
  rw [← ht]
  simp only [smul_apply, smul_comm c (ρ ^ j),
    identityLeakageJetAmplitude, graphOutputSymbolJet]
  congr 1
  dsimp only [c, g]
  simp only [smul_eq_mul]
  ring

/-- Exact Fourier representation of every output derivative of the SAME
identity kernel. The fixed scale loss is `ρ^(n+j)`; the frequency amplitude
is the already checked complementary graph-symbol jet, not a new operator
(`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_identityLeakageScalarKernel_apply_eq_fourier {ρ : ℝ} (hρ : 0 < ρ)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (j : ℕ) (v : Fin j → E) (x y : E) :
    iteratedFDeriv ℝ j (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) x v =
      (((ρ / (2 * Real.pi)) ^ n) * ρ ^ j : ℝ) •
        𝓕 (identityLeakageJetAmplitude ρ mi mo x y j v)
          (-(ρ / (2 * Real.pi)) • (x - y)) := by
  let f : E × E → ℂ := fun p ↦
    Complex.exp ((ρ * inner ℝ (p.1 - y) p.2 : ℝ) * Complex.I) *
      (1 - (mo (p.1, p.2) : ℂ)) * (mi (y, p.2) : ℂ)
  have hf : ContDiff ℝ ∞ f :=
    ((Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
        ((contDiff_fst.sub contDiff_const).inner ℝ contDiff_snd))).mul contDiff_const)).mul
      (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp ho))).mul
      (Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_const.prodMk contDiff_snd)))
  have hs z η (hη : η ∉ Prod.snd '' tsupport mi) : f (z, η) = 0 := by
    have hz : mi (y, η) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hη ⟨(y, η), h, rfl⟩)
    simp [f, hz]
  have he : (fun z ↦ identityLeakageScalarKernel ρ mi mo z y) =
      fun z ↦ ((ρ / (2 * Real.pi)) ^ n : ℝ) • ∫ η, f (z, η) :=
    funext (fun z ↦ identityLeakageScalarKernel_eq_normalizedIntegral hρ mi mo z y)
  rw [he, iteratedFDeriv_const_smul_apply'
    ((contDiff_integral_commonCarrier hf (his.image continuous_snd) hs).contDiffAt.of_le (by simp)),
    iteratedFDeriv_integral_commonCarrier hf (his.image continuous_snd) hs,
    smul_apply,
    ContinuousMultilinearMap.integral_apply
      (integrable_outputJet_commonCarrier hf (his.image continuous_snd) hs j x)]
  simp_rw [show ∀ η, iteratedFDeriv ℝ j (fun z ↦ f (z, η)) x v =
    ρ ^ j • (Complex.exp ((ρ * inner ℝ (x - y) η : ℝ) * Complex.I) *
      identityLeakageJetAmplitude ρ mi mo x y j v η) from
      fun η ↦ identityLeakage_integrand_outputJet hρ.ne' mi mo ho x y η j v]
  rw [integral_smul, smul_smul, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  have hp : -2 * Real.pi * inner ℝ η (-(ρ / (2 * Real.pi)) • (x - y)) =
      ρ * inner ℝ (x - y) η := by
    rw [inner_smul_right, real_inner_comm η (x - y)]
    field_simp
  simp only [hp, smul_eq_mul]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
