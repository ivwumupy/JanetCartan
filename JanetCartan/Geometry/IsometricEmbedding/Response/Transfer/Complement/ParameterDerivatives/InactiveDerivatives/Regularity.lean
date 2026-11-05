module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.LocalIntegral

/-!
# Regularity and support of the actual differentiated carrier

Primitive phase/source data imply the smoothness and common support required
for the inactive derivative source in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The original spatial support contains the carrier source support
(`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_parameterSourceFunction_subset (ρ : ℝ) (φ : P → E → ℝ)
    (f : P → E → F) (c : P) :
    tsupport (parameterSourceFunction ρ φ f c) ⊆ tsupport (f c) :=
  tsupport_smul_subset_right _ _

/-- Primitive joint phase smoothness near the fixed source support implies
joint smoothness of the same supported carrier globally. No phase extension is
required (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_parameterSourceFunction_localized
    {V : Set P} {U K : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K) :
    ContDiffOn ℝ ∞ (Function.uncurry (parameterSourceFunction ρ φ f))
      (V ×ˢ univ) := by
  intro z hz
  by_cases hx : z.2 ∈ U
  · have hp := hφ.contDiffAt ((hV.prod hU).mem_nhds ⟨hz.1, hx⟩)
    have hfc := hf.contDiffAt ((hV.prod isOpen_univ).mem_nhds hz)
    exact (((contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hp))).cexp).smul
        hfc).contDiffWithinAt
  · have hn : z.2 ∉ K := fun hk ↦ hx (hKU hk)
    have he : Function.uncurry (parameterSourceFunction ρ φ f) =ᶠ[𝓝 z]
        fun _ ↦ (0 : F) := by
      filter_upwards [continuousAt_fst.preimage_mem_nhds (hV.mem_nhds hz.1),
        continuousAt_snd.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hn)] with a ha hax
      have hz : f a.1 a.2 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hax (hs a.1 ha h))
      change carrier ρ (φ a.1) a.2 • f a.1 a.2 = 0
      rw [hz, smul_zero]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- The normalized actual jet is spatially smooth, derived from the original
phase/source smoothness and fixed support. Consumer: the differentiated envelope
in `InactiveSource.masked_carrierSource_arbitrary_precision`; source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem contDiff_parameterCarrierJet_of_original
    {V : Set P} {U K : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    ContDiff ℝ ∞ (parameterCarrierJet ρ φ f k v c) := by
  have hj := contDiffOn_parameterSourceFunction_localized hV hU hK.isClosed hKU ρ hφ hf hs
  have hsupport : ∀ a ∈ V, tsupport (parameterSourceFunction ρ φ f a) ⊆ K :=
    fun a ha ↦ (tsupport_parameterSourceFunction_subset ρ φ f a).trans (hs a ha)
  have hsjet := tsupport_parameterCarrierJet_subset hK hV ρ φ f k v hc hsupport
  apply JanetCartan.Localization.contDiff_of_contDiffOn_support_neighborhood hU _
    (hsjet.trans hKU)
  change ContDiffOn ℝ ∞ (fun x ↦ carrier (-ρ) (φ c) x •
    iteratedFDeriv ℝ k (fun a ↦ parameterSourceFunction ρ φ f a x) c v) U
  have hd := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ P) F v).contDiff.comp_contDiffOn
    (contDiffOn_parameterIteratedFDeriv hV hj k)
  have hdx : ContDiffOn ℝ ∞ (fun x ↦ iteratedFDeriv ℝ k
      (fun a ↦ parameterSourceFunction ρ φ f a x) c v) U :=
    hd.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x _ ↦ ⟨hc, mem_univ x⟩)
  have hpx : ContDiffOn ℝ ∞ (φ c) U :=
    hφ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨hc, hx⟩)
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul hpx))).cexp).smul hdx

/-- Actual parameter differentiation preserves the support of the original
source family; its carrier adds no support. This supplies both source cutoff
plateaus (`app:ch_response:thm:response-literal-transfer`). -/
theorem tsupport_parameterCarrierJet_subset_original
    {V : Set P} {K : Set E} (hV : IsOpen V) (hK : IsCompact K)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    tsupport (parameterCarrierJet ρ φ f k v c) ⊆ K :=
  tsupport_parameterCarrierJet_subset hK hV ρ φ f k v hc
    (fun a ha ↦ (tsupport_parameterSourceFunction_subset ρ φ f a).trans (hs a ha))

/-- Compact support of the actual normalized jet, derived from the original
common support (`app:ch_response:thm:response-literal-transfer`). -/
theorem hasCompactSupport_parameterCarrierJet_of_original
    {V : Set P} {K : Set E} (hV : IsOpen V) (hK : IsCompact K)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    HasCompactSupport (parameterCarrierJet ρ φ f k v c) :=
  hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_parameterCarrierJet_subset_original hV hK ρ φ f hs k v hc)

/-- The differentiated demodulated envelope is genuinely in the original
Euclidean vector L² space, without a jet membership premise
(`app:ch_response:thm:response-literal-transfer`). -/
theorem memLp_parameterCarrierJet_of_original
    {V : Set P} {U K : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    MeasureTheory.MemLp (parameterCarrierJet ρ φ f k v c) 2 MeasureTheory.volume :=
  (contDiff_parameterCarrierJet_of_original hV hU hK hKU ρ hφ hf hs k v hc).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_parameterCarrierJet_of_original hV hK ρ φ f hs k v hc)

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
