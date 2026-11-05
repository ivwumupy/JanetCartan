module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.TranslatedNormal
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization

/-!
# Extending the phase on the full normal segments

The graph-normal calculus for `app:ch_response:eq:direct-envelope-profile`
requires a continuous global phase. A phase smooth only on a buffered chart
has a smooth extension near a compact set containing every supported physical
segment. The original normal chart, its inverse and its determinant gap are
preserved. There is no smoothness assumption at the zero covector outside the
original chart, and both physical output positions remain in the hypotheses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer

open NormalComparison FourierIntegral.LowBounds

variable {n : ℕ}
local notation "E" => Euclidean n

/-- Local agreement along the entire physical segment preserves the actual
averaged normal map (`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedGradient_eq_of_segment_eventuallyEq
    (S S' : E → E → ℝ) (x y u : E)
    (he : ∀ t ∈ uIcc (0 : ℝ) 1,
      (fun z ↦ S' z u) =ᶠ[𝓝 (y + t • (x - y))] (fun z ↦ S z u)) :
    averagedGradient S' x y u = averagedGradient S x y u := by
  unfold averagedGradient averagedPhaseDifferential
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (he t (by simpa using ht)).fderiv_eq

/-- Every primitive field of the spatial normal chart is preserved by a local
phase extension on the supported segments. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem averagedGradientChart_of_segment_eventuallyEq
    {S S' : E → E → ℝ} {X D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {g : ℝ}
    (G : AveragedGradientChart S X D η J g)
    (he : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
      (fun z ↦ S' z u) =ᶠ[𝓝 (y + t • (x - y))] (fun z ↦ S z u)) :
    AveragedGradientChart S' X D η J g := by
  have hm (x : E) (hx : x ∈ X) (y : E) (hy : y ∈ X) (u : E) (hu : u ∈ D) :=
    averagedGradient_eq_of_segment_eventuallyEq S S' x y u (he x hx y hy u hu)
  refine ⟨G.measurable, G.gap_pos, ?_, ?_, ?_, ?_, ?_, G.gap⟩
  · intro x hx y hy u hu t ht
    exact (G.segment x hx y hy u hu t ht).congr_of_eventuallyEq (he x hx y hy u hu t ht)
  · intro x hx y hy u hu
    apply (G.integrable x hx y hy u hu).congr
    intro t ht
    exact (he x hx y hy u hu t (uIoc_subset_uIcc ht)).fderiv_eq.symm
  · intro x hx y hy u hu
    exact (G.derivative x hx y hy u hu).congr' (fun v hv ↦ hm x hx y hy v hv) hu
  · intro x hx y hy u hu v hv huv
    apply G.injective x hx y hy hu hv
    simpa only [hm x hx y hy u hu, hm x hx y hy v hv] using huv
  · intro x hx y hy u hu
    rw [hm x hx y hy u hu]
    exact G.leftInverse x hx y hy u hu

/-- Construct the globally smooth phase needed by the low graph theorem,
preserving every primitive jet near a compact carrier containing the complete
supported physical segments. The buffered set and its compactness are primitive
geometric inputs; a global extension or a preserved normal chart is not assumed.
Consumer: the literal translated-phase low estimate in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_nearCarrierPhaseExtension
    {S : E → E → ℝ} {X D : Set E} {η : E → E → E → E}
    {J : E → E → E → E →L[ℝ] E} {g : ℝ}
    (G : AveragedGradientChart S X D η J g)
    {U K : Set (E × E)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) U)
    (hseg : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, ∀ t ∈ uIcc (0 : ℝ) 1,
      (y + t • (x - y), u) ∈ K) :
    ∃ S' : E → E → ℝ,
      ContDiff ℝ ∞ (Function.uncurry S') ∧
      (∀ p ∈ K, Function.uncurry S' =ᶠ[𝓝 p] Function.uncurry S) ∧
      (∀ p ∈ K, ∀ k, iteratedFDeriv ℝ k (Function.uncurry S') p =
        iteratedFDeriv ℝ k (Function.uncurry S) p) ∧
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, averagedGradient S' x y u = averagedGradient S x y u) ∧
      AveragedGradientChart S' X D η J g ∧
      ∀ ζ ρ, ρ • ζ ∈ D →
        ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S' ζ ρ)) ∧
        (∀ x ∈ X, ∀ δ ∈ translatedCovectorDomain D ζ ρ,
          phaseIncrement S' ζ ρ x δ = phaseIncrement S ζ ρ x δ) ∧
        AveragedGradientChart (phaseIncrement S' ζ ρ) X (translatedCovectorDomain D ζ ρ)
          (translatedNormalInverse S η ζ ρ) (translatedNormalJacobian J ζ ρ) g := by
  obtain ⟨f, hf, _, _, _, he⟩ := exists_contDiff_localization hU hK hKU hS
  let S' : E → E → ℝ := fun x u ↦ f (x, u)
  have he' (x : E) (hx : x ∈ X) (y : E) (hy : y ∈ X) (u : E) (hu : u ∈ D)
      (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      (fun z ↦ S' z u) =ᶠ[𝓝 (y + t • (x - y))] (fun z ↦ S z u) :=
    (he _ (hseg x hx y hy u hu t ht)).comp_tendsto
      (continuousAt_id.prodMk continuousAt_const).tendsto
  have hG : AveragedGradientChart S' X D η J g :=
    averagedGradientChart_of_segment_eventuallyEq G he'
  have hpoint (x : E) (hx : x ∈ X) (u : E) (hu : u ∈ D) : S' x u = S x u := by
    simpa using (he' x hx x hx u hu 0 (by simp)).eq_of_nhds
  refine ⟨S', hf, he, ?_, ?_, hG, ?_⟩
  · intro p hp k
    exact ((he p hp).iteratedFDeriv ℝ k).eq_of_nhds
  · intro x hx y hy u hu
    exact averagedGradient_eq_of_segment_eventuallyEq S S' x y u (he' x hx y hy u hu)
  · intro ζ ρ hcentral
    refine ⟨?_, ?_, ?_⟩
    · exact (hf.comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))).sub
        (hf.comp (contDiff_fst.prodMk contDiff_const))
    · intro x hx δ hδ
      simp only [phaseIncrement, hpoint x hx _ hδ, hpoint x hx _ hcentral]
    · have hnew := averagedGradientChart_phaseIncrement hG ζ ρ hcentral
      refine { hnew with leftInverse := ?_ }
      intro x hx y hy δ hδ
      have hc := averagedGradient_eq_of_segment_eventuallyEq S S' x y (ρ • ζ)
        (he' x hx y hy _ hcentral)
      simpa only [translatedNormalInverse, hc] using hnew.leftInverse x hx y hy δ hδ

end JanetCartan.ResponseTransfer
