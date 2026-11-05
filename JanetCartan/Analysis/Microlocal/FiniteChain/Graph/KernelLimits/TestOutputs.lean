module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Output.CompactKernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fourier
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Repacking
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ForwardRegularized.CompactKernel

/-!
# Smooth graph test outputs before output cutoff removal

For `app:ch_regular:eq:joint-kernel-phase`, the right localizer and a compact
frequency graph factor produce a smooth compact field. Fourier inversion can
therefore recover the actual identity-minus-output-localizer. Compact support
is asserted after this limit, not for the regularized identity kernels.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
open Retarded.KernelDecay
variable {n r : ℕ}
attribute [local fun_prop] ContDiff.inner
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem smooth_iterated_integral
    (F : Euclidean n × (Euclidean n × Euclidean n) → Fin r → ℂ)
    (hF : ContDiff ℝ ∞ F) (K Y : Set (Euclidean n)) (hK : IsCompact K) (hY : IsCompact Y)
    (hsK : ∀ x ξ z, ξ ∉ K → F (x, ξ, z) = 0)
    (hsY : ∀ x ξ z, z ∉ Y → F (x, ξ, z) = 0) :
    ContDiff ℝ ∞ (fun x => ∫ ξ, ∫ z, F (x, ξ, z)) := by
  have hi : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n => ∫ z, F (p.1, p.2, z)) :=
    contDiff_integral_commonCarrier
      (hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))) hY
      (fun p z hz => hsY p.1 p.2 z hz)
  exact contDiff_integral_commonCarrier hi hK (fun x ξ hξ => by simp [hsK x ξ _ hξ])

/-- Smoothness of the actual right quantization from compact primitive
input carriers. This supplies the datum regularity for the graph factor in
`app:ch_regular:eq:joint-kernel-phase`. -/
theorem contDiff_rightLocalizer
    (A : FullAmplitude n r) (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (hi : ContDiff ℝ ∞ mi)
    (f : Euclidean n → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rightLocalizer 1 mi f) := by
  change Euclidean n × Euclidean n → ℝ at mi
  let F : Euclidean n × (Euclidean n × Euclidean n) → Fin r → ℂ := fun p =>
    (graphOscillation (fun a b => inner ℝ a b) p.1 p.2.2 p.2.1 *
      (mi (p.2.2, p.2.1) : ℂ)) • f p.2.2
  have hF : ContDiff ℝ ∞ F := by
    change ContDiff ℝ ∞ (mi : Euclidean n × Euclidean n → ℝ) at hi
    have hp : ContDiff ℝ ∞ (fun p : Euclidean n × (Euclidean n × Euclidean n) =>
        inner ℝ p.1 p.2.1 - inner ℝ p.2.2 p.2.1) := by fun_prop
    exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp.mul
      (Complex.ofRealCLM.contDiff.comp (hi.comp (contDiff_snd.snd.prodMk contDiff_snd.fst)))).smul
      (hf.comp contDiff_snd.snd)
  have hs := smooth_iterated_integral F hF c.inputFrequency c.inputBase
    c.compact_inputFrequency c.compact_inputBase
    (fun x ξ z hξ => by simp [F, c.input_zero z ξ (fun h => hξ h.2)])
    (fun x ξ z hz => by simp [F, c.input_zero z ξ (fun h => hz h.1)])
  change ContDiff ℝ ∞ (fun x => rightLocalizer 1 mi f x)
  simp only [rightLocalizer, inv_one, one_smul, graphOperator, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul]
  simpa only [Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul, F] using hs.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- Compact output support of the frequency-regularized forward graph factor,
using the first physical amplitude position (`app:ch_regular:eq:chain-tail`). -/
theorem regularizedGraph_hasCompactSupport
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (g : Euclidean n → Fin r → ℂ) :
    HasCompactSupport (graphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) g) := by
  apply HasCompactSupport.intro (c.compact_amplitudeBase.image continuous_fst)
  intro x hx
  have hz (z ξ : Euclidean n) : A x z ξ = 0 :=
    c.amplitude_zero x z ξ (fun h => hx ⟨(x,z), h, rfl⟩)
  simp [graphOperator, hz]

/-- Compact output support of the frequency-regularized literal reverse,
using the second physical amplitude position (`app:ch_regular:eq:chain-tail`). -/
theorem regularizedReverseGraph_hasCompactSupport
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (g : Euclidean n → Fin r → ℂ) :
    HasCompactSupport (reverseGraphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) g) := by
  apply HasCompactSupport.intro (c.compact_amplitudeBase.image continuous_snd)
  intro z hz
  have hu (u ξ : Euclidean n) : A u z ξ = 0 :=
    c.amplitude_zero u z ξ (fun h => hz ⟨(u,z), h, rfl⟩)
  simp [reverseGraphOperator, hu]

/-- Smoothness of the actual regularized forward graph output on smooth
inputs. The compact amplitude carrier replaces any compact-support requirement
on the right-localized input. The phase is differentiated only away from zero
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_regularizedGraph
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hχ : ContDiff ℝ ∞ χA) (hχ0 : (0 : Euclidean n) ∉ tsupport χA)
    (g : Euclidean n → Fin r → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (graphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) g) := by
  let B : FullAmplitude n r := fun u z ξ => (χA ξ : ℂ) • A u z ξ
  have hB : ForwardAmplitudeAdmissible (Prod.fst '' c.amplitudeBase)
      (Prod.snd '' c.amplitudeBase) (tsupport χA) B := by
    constructor
    · exact (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd.snd)).smul
        (hA.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))
    · intro u z ξ h
      rcases h with hu | hz | hξ
      · simp [B, c.amplitude_zero u z ξ (fun h => hu ⟨(u,z), h, rfl⟩)]
      · simp [B, c.amplitude_zero u z ξ (fun h => hz ⟨(u,z), h, rfl⟩)]
      · simp [B, image_eq_zero_of_notMem_tsupport hξ]
  have hi := ForwardRegularized.smooth_integrand hB (isClosed_tsupport χA) hχ0 hS hg
  have hs := smooth_iterated_integral (ForwardRegularized.integrand S B g) hi
    (tsupport χA) (Prod.snd '' c.amplitudeBase) c.compact_graphCutoff
    (c.compact_amplitudeBase.image continuous_snd)
    (fun x ξ z hξ => by simp [ForwardRegularized.integrand, hB.support x z ξ (Or.inr (Or.inr hξ))])
    (fun x ξ z hz => by simp [ForwardRegularized.integrand, hB.support x z ξ (Or.inr (Or.inl hz))])
  exact hs.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)


/-- Smoothness of the actual compact-frequency reverse graph output, retaining
both original amplitude positions. As in the forward case, the source carrier
comes from the amplitude, not from the right-localized field
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_regularizedReverseGraph
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hχ : ContDiff ℝ ∞ χA) (hχ0 : (0 : Euclidean n) ∉ tsupport χA)
    (g : Euclidean n → Fin r → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (reverseGraphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) g) := by
  have hC : ReverseAmplitudeAdmissible c.amplitudeBase A := by
    constructor
    · exact fun _ _ => hA.contDiffAt
    · apply closure_minimal
      · intro p hp
        by_contra hn
        exact hp (c.amplitude_zero p.1.1 p.1.2 p.2 hn)
      · exact c.compact_amplitudeBase.isClosed.preimage continuous_fst
  have hχ0' : (0 : Euclidean n) ∉ tsupport (fun ξ => (χA ξ : ℂ)) := by
    simpa [tsupport, Function.support] using hχ0
  have hi := ReverseRegularized.Output.smooth_integrand hC hS
    (Complex.ofRealCLM.contDiff.comp hχ) hχ0' hg
  have hs := smooth_iterated_integral
    (ReverseRegularized.Output.integrand S (frequencyCutFullAmplitude (fun ξ => (χA ξ : ℂ)) A) g)
    hi (tsupport χA) (Prod.fst '' c.amplitudeBase) c.compact_graphCutoff
    (c.compact_amplitudeBase.image continuous_fst)
    (fun z ξ u hξ => by simp [ReverseRegularized.Output.integrand, frequencyCutFullAmplitude,
      image_eq_zero_of_notMem_tsupport hξ])
    (fun z ξ u hu => by simp [ReverseRegularized.Output.integrand, frequencyCutFullAmplitude,
      c.amplitude_zero u z ξ (fun h => hu ⟨(u,z), h, rfl⟩)])
  exact hs.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)

/-- Removing the output-frequency regularizer from the actual forward joint
kernel recovers the literal identity-minus-localizer, for a fixed compact graph
frequency cutoff. Smoothness and support of the graph output are derived from
primitive data; the identity term is recovered by Fourier inversion
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem tendsto_forwardJointKernel_outputCutoff
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA : Euclidean n → ℝ) (χo : ℕ → Euclidean n → ℝ)
    (c : ∀ k, RegularizedCarriers A mi χA (χo k))
    (hSc : Continuous (Function.uncurry S))
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (hχA : ContDiff ℝ ∞ χA) (hχA0 : (0 : Euclidean n) ∉ tsupport χA)
    (hχo : ∀ k, Continuous (χo k)) (hχob : ∀ k ξ, |χo k ξ| ≤ 1)
    (hχolim : ∀ ξ, Tendsto (fun k => χo k ξ) atTop (𝓝 1))
    (B : ℝ) (hb : ∀ x ξ, |mo (x,ξ)| ≤ B)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (f : Euclidean n → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) :
    (∀ x, Tendsto (fun k => ∫ y,
      (regularizedJointKernel false S A mi mo χA (χo k) x y).mulVec (f y)) atTop
        (𝓝 (forwardLeakage S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) 1 mi mo f x))) ∧
      HasCompactSupport (forwardLeakage S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) 1 mi mo f) := by
  have hg := contDiff_regularizedGraph S A mi χA (χo 0) (c 0) hS hA hχA hχA0
    (rightLocalizer 1 mi f) (contDiff_rightLocalizer A mi χA (χo 0) (c 0) hi f hf)
  have hgs := regularizedGraph_hasCompactSupport S A mi χA (χo 0) (c 0) (rightLocalizer 1 mi f)
  obtain ⟨hlim, hs⟩ := tendsto_regularized_complementary_output 1 mo _ hg hgs ho B hb t ht hmt
    χo hχo hχob hχolim one_ne_zero
  refine ⟨fun x => ?_, hs⟩
  have he (k : ℕ) := forward_composition_eq_jointKernel S A mi mo χA (χo k)
    hSc hA.continuous hi.continuous ho hχA.continuous (hχo k) (c k) f hf.continuous x
  simpa only [one_smul, he, forwardLeakage, Pi.sub_apply] using hlim x

/-- Removing the output-frequency regularizer from the actual reverse joint
kernel recovers the literal identity-minus-localizer, for a fixed compact graph
frequency cutoff. Smoothness and support of the graph output are derived from
primitive data; the identity term is recovered by Fourier inversion
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem tendsto_reverseJointKernel_outputCutoff
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA : Euclidean n → ℝ) (χo : ℕ → Euclidean n → ℝ)
    (c : ∀ k, RegularizedCarriers A mi χA (χo k))
    (hSc : Continuous (Function.uncurry S))
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (hχA : ContDiff ℝ ∞ χA) (hχA0 : (0 : Euclidean n) ∉ tsupport χA)
    (hχo : ∀ k, Continuous (χo k)) (hχob : ∀ k ξ, |χo k ξ| ≤ 1)
    (hχolim : ∀ ξ, Tendsto (fun k => χo k ξ) atTop (𝓝 1))
    (B : ℝ) (hb : ∀ x ξ, |mo (x,ξ)| ≤ B)
    (t : Set (Euclidean n)) (ht : IsCompact t)
    (hmt : ∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0)
    (f : Euclidean n → Fin r → ℂ) (hf : ContDiff ℝ ∞ f) :
    (∀ x, Tendsto (fun k => ∫ y,
      (regularizedJointKernel true S A mi mo χA (χo k) x y).mulVec (f y)) atTop
        (𝓝 (reverseLeakage S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) 1 mi mo f x))) ∧
      HasCompactSupport (reverseLeakage S (fun u z ξ => (χA ξ : ℂ) • A u z ξ) 1 mi mo f) := by
  have hg := contDiff_regularizedReverseGraph S A mi χA (χo 0) (c 0) hS hA hχA hχA0
    (rightLocalizer 1 mi f) (contDiff_rightLocalizer A mi χA (χo 0) (c 0) hi f hf)
  have hgs := regularizedReverseGraph_hasCompactSupport S A mi χA (χo 0) (c 0) (rightLocalizer 1 mi f)
  obtain ⟨hlim, hs⟩ := tendsto_regularized_complementary_output 1 mo _ hg hgs ho B hb t ht hmt
    χo hχo hχob hχolim one_ne_zero
  refine ⟨fun x => ?_, hs⟩
  have he (k : ℕ) := reverse_composition_eq_jointKernel S A mi mo χA (χo k)
    hSc hA.continuous hi.continuous ho hχA.continuous (hχo k) (c k) f hf.continuous x
  simpa only [one_smul, he, reverseLeakage, Pi.sub_apply] using hlim x
end JanetCartan.FiniteChain.Graph.KernelLimits
