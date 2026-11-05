module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SourceParameterCoordinates.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets

/-!
# Actual regularity and L² classes in the original source parameters

The parameter split changes neither the spatial variable nor its measure.
The Euclidean source construction therefore supplies regularity, compact
support, and true L² derivatives for the original product parameters in
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse
open ResponseTransfer ResponseTransfer.FullSourceEnvelopes
open ResponseTransfer.Complement ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential FourierIntegral

variable {d r : ℕ}
local notation "P" => Euclidean 3 × Euclidean d
local notation "Pc" => Euclidean (3+d)
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "splitP" => (EuclideanSpace.finAddEquivProd : Pc ≃L[ℝ] P)

private theorem pullback_joint_contDiffOn
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {V : Set P} {U : Set E} {f : P → E → Z}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun a : Pc ↦ f (splitP a)))
      ((splitP ⁻¹' V) ×ˢ U) :=
  hf.comp (((splitP).prodCongr (ContinuousLinearEquiv.refl ℝ E)).contDiff.contDiffOn)
    (fun _ h ↦ ⟨h.1, h.2⟩)

/-- Joint smoothness of the whole original carrier/source follows from the
given phase, amplitude, and common support, even when the phase is smooth
only on the original spatial neighborhood. This is the input to the actual
L² source derivative in `app:ch_response:thm:response-literal-transfer`. -/
theorem contDiffOn_productParameterSourceFunction_localized
    {V : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ S) :
    ContDiffOn ℝ ∞
      (Function.uncurry (fun c x ↦ carrier ρ (φ c) x • f c x)) (V ×ˢ univ) := by
  let pe := (splitP).prodCongr (ContinuousLinearEquiv.refl ℝ E)
  have hphysical := contDiffOn_parameterSourceFunction_localized
    (hV.preimage (splitP).continuous) hU hS hSU ρ
    (pullback_joint_contDiffOn hφ) (pullback_joint_contDiffOn hf)
    (fun a ha ↦ hs (splitP a) ha)
  have hmap : MapsTo pe.symm (V ×ˢ (univ : Set E)) ((splitP ⁻¹' V) ×ˢ univ) := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    exact ⟨by simpa [pe] using ha, hx⟩
  have hfun :
      Function.uncurry (parameterSourceFunction ρ (fun a ↦ φ (splitP a))
        (fun a ↦ f (splitP a))) ∘ pe.symm =
      Function.uncurry (fun c x ↦ carrier ρ (φ c) x • f c x) := by
    funext w
    rcases w with ⟨a, x⟩
    simp [pe, parameterSourceFunction]
  rw [← hfun]
  exact hphysical.comp pe.symm.contDiff.contDiffOn hmap

/-- Spatial smoothness of the literal product-parameter normalized jet is
obtained from the original source hypotheses, with no smooth-output premise
(`app:ch_response:eq:response-graded-reduced`). -/
theorem contDiff_productParameterCarrierJet_of_original
    {V : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ S)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    ContDiff ℝ ∞ (productParameterCarrierJet ρ φ f k v c) := by
  rw [productParameterCarrierJet_eq_coordinate]
  exact contDiff_parameterCarrierJet_of_original (hV.preimage (splitP).continuous)
    hU hS hSU ρ (pullback_joint_contDiffOn hφ) (pullback_joint_contDiffOn hf)
    (fun a ha ↦ hs (splitP a) ha) k (fun i ↦ (splitP).symm (v i))
    (by simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hc)

/-- Parameter differentiation preserves the original compact spatial support
under the same coordinate split (`app:ch_response:eq:response-graded-source`). -/
theorem tsupport_productParameterCarrierJet_subset_original
    {V : Set P} {S : Set E} (hV : IsOpen V) (hS : IsCompact S)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ S)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    tsupport (productParameterCarrierJet ρ φ f k v c) ⊆ S := by
  rw [productParameterCarrierJet_eq_coordinate]
  exact tsupport_parameterCarrierJet_subset_original (hV.preimage (splitP).continuous)
    hS ρ _ _ (fun a ha ↦ hs (splitP a) ha) k (fun i ↦ (splitP).symm (v i))
    (by simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hc)

/-- The original normalized parameter jet has its actual vector L² class
(`app:ch_response:thm:response-literal-transfer`). -/
theorem memLp_productParameterCarrierJet_of_original
    {V : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ S)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    MemLp (productParameterCarrierJet ρ φ f k v c) 2 volume :=
  (contDiff_productParameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v hc).continuous.memLp_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_productParameterCarrierJet_subset_original hV hS ρ φ f hs k v hc))

/-- Every Fourier-Sobolev membership is for that same original L² class;
no new representative is selected (`app:ch_response:eq:response-graded-reduced`). -/
theorem memVectorFourierSobolev_productParameterCarrierJet_of_original
    {V : Set P} {U S : Set E} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) (ρ : ℝ)
    {φ : P → E → ℝ} {f : P → E → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ S)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) (s : ℝ) :
    MemVectorFourierSobolev s
      ((memLp_productParameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v hc).toLp
        (productParameterCarrierJet ρ φ f k v c)) := by
  let u : graphTestSpace (d+1) r := ⟨productParameterCarrierJet ρ φ f k v c,
    contDiff_productParameterCarrierJet_of_original hV hU hS hSU ρ hφ hf hs k v hc,
    hS.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_productParameterCarrierJet_subset_original hV hS ρ φ f hs k v hc)⟩
  exact graphTest_memVectorFourierSobolev s u

/-- The true derivative of the original product-parameter L² source is the
L² class of its pointwise derivative. This applies to the whole modulated
source after `contDiffOn_productParameterSourceFunction_localized`; the
measure and original parameter tuple are unchanged
(`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_productParameterSourceClass
    {S : Set E} (hS : IsCompact S) {V : Set P} (hV : IsOpen V)
    {g : P → E → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ S)
    (hm : ∀ a, MemLp (g a) 2 volume)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    iteratedFDeriv ℝ k (fun a ↦ (hm a).toLp (g a)) c v =
      (fullSource_parameterJet_memLp hS hV hg hs k v hc).toLp
        (fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v) := by
  have hc' : (splitP).symm c ∈ splitP ⁻¹' V := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hc
  have hclass := iteratedFDeriv_parameterSourceClass hS (hV.preimage (splitP).continuous)
    (pullback_joint_contDiffOn hg) (fun a ha ↦ hs (splitP a) ha)
    (fun a ↦ hm (splitP a)) k (fun i ↦ (splitP).symm (v i)) hc'
  have hcoord := congrArg (fun D ↦ D (fun i ↦ (splitP).symm (v i)))
    (externalCoordinate_jet splitP (fun a ↦ (hm a).toLp (g a)) ((splitP).symm c) k)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hcoord
  rw [← hcoord]
  simp only [Function.comp_def]
  rw [hclass]
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
    congrArg (fun D ↦ D (fun i ↦ (splitP).symm (v i)))
      (externalCoordinate_jet splitP (fun a ↦ g a x) ((splitP).symm c) k)

/-- The original product-parameter source is jointly smooth as an L²-valued
map, from its given smooth compact spatial realization. This supplies the
smoothness needed to identify ordered words with the actual derivatives,
without a smooth-output hypothesis
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_productParameterSourceClass
    {S : Set E} (hS : IsCompact S) {V : Set P} (hV : IsOpen V)
    {g : P → E → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ S)
    (hm : ∀ a, MemLp (g a) 2 volume) :
    ContDiffOn ℝ ∞ (fun a ↦ (hm a).toLp (g a)) V := by
  apply contDiffOn_infty.mpr
  intro k c hc
  have hc' : (splitP).symm c ∈ splitP ⁻¹' V := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hc
  have hcoord := contDiffAt_parameterSourceClass hS (hV.preimage (splitP).continuous)
    (pullback_joint_contDiffOn hg) (fun a ha ↦ hs (splitP a) ha)
    (fun a ↦ hm (splitP a)) k hc'
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
    (hcoord.comp c (splitP).symm.contDiff.contDiffAt).contDiffWithinAt

end JanetCartan.FixedDomainInverse
