module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.Basic

/-!
# Phase locality for supported weak identities

The auxiliary phase below is used only to justify compact kernel calculus.
It agrees with the original phase on a neighborhood of the closed carrier.
No homogeneity or nondegeneracy is asserted outside that carrier.
The consumer is the literal adjoint weak identity in
`app:ch_regular_base:eq:actual-adjoint-trade`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev
open FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Projecting away the spectator source position gives a smooth auxiliary
phase agreeing on the entire closed conic carrier. Its sole consumer is compact
kernel differentiation in the supported weak identities.
Source: the buffered-chart paragraph following actual-calculus item (4). -/
theorem exists_smooth_supported_phase_extension
    {K : Set (E × E)} {F : Set E} {U : Set (Point n)}
    (hK : IsCompact K) (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hU : IsOpen U) (hcarrier : K ×ˢ F ⊆ U)
    (S : E → E → ℝ) (hS : SupportedPhaseRegularity S U) :
    ∃ S' : E → E → ℝ, ContDiff ℝ ∞ (Function.uncurry S') ∧
      ∀ p ∈ K ×ˢ F, Function.uncurry S' =ᶠ[𝓝 (p.1.1, p.2)] Function.uncurry S := by
  let O : Set (E × E) := ⋃ y : E, {q | ((q.1, y), q.2) ∈ U ∧ q.2 ≠ 0}
  have hO : IsOpen O := by
    apply isOpen_iUnion
    intro y
    exact (hU.preimage ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)).inter
      (isClosed_singleton.isOpen_compl.preimage continuous_snd)
  have hKO : (Prod.fst '' K) ×ˢ F ⊆ O := by
    rintro ⟨x, η⟩ ⟨⟨⟨x', y⟩, hp, rfl⟩, hη⟩
    exact mem_iUnion.mpr ⟨y, hcarrier ⟨hp, hη⟩, fun hz ↦ hF0 (hz ▸ hη)⟩
  have hs : ContDiffOn ℝ ∞ (Function.uncurry S) O := by
    intro q hq
    obtain ⟨y, hy, hη⟩ := mem_iUnion.mp hq
    exact (hS ((q.1, y), q.2) hy hη).contDiffWithinAt
  obtain ⟨S', hs', he⟩ := exists_smooth_phase_extension S
    ((hK.image continuous_fst).isClosed.prod hF) hO hKO hs
  refine ⟨S', hs', ?_⟩
  intro p hp
  exact he (p.1.1, p.2) ⟨⟨p.1, hp.1, rfl⟩, hp.2⟩

/-- Germ agreement preserves the physical phase derivative, before any
homogeneity trade. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem phase_outputPartial_eventuallyEq {S S' : E → E → ℝ} {x η : E}
    (h : Function.uncurry S' =ᶠ[𝓝 (x, η)] Function.uncurry S) (i : Fin n) :
    (fun q : E × E ↦ partialDeriv (fun z ↦ S' z q.2) q.1 i) =ᶠ[𝓝 (x, η)]
      (fun q : E × E ↦ partialDeriv (fun z ↦ S z q.2) q.1 i) := by
  filter_upwards [h.eventually_nhds] with q hq
  change Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S at hq
  have he := hq.comp_tendsto (continuousAt_id.prodMk (continuousAt_const (y := q.2)))
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
    (he.fderiv_eq (𝕜 := ℝ))

/-- The mixed matrix, including its actual inverse, is unchanged on the
supported chart. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem mixedPhaseMatrix_eq_of_eventuallyEq {S S' : E → E → ℝ} {x η : E}
    (h : Function.uncurry S' =ᶠ[𝓝 (x, η)] Function.uncurry S) :
    mixedPhaseMatrix S' x η = mixedPhaseMatrix S x η := by
  ext i j
  have he := (phase_outputPartial_eventuallyEq h i).comp_tendsto
    ((continuousAt_const (y := x)).prodMk continuousAt_id)
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (EuclideanSpace.single j 1))
    (he.fderiv_eq (𝕜 := ℝ))

/-- Local radial homogeneity transfers through germ agreement, only at the
point where the original phase satisfies it. No global homogeneous extension
is used. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem phase_homogeneity_of_eventuallyEq {S S' : E → E → ℝ} {x η : E}
    (h : Function.uncurry S' =ᶠ[𝓝 (x, η)] Function.uncurry S)
    (hh : ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η)) :
    ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S' z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S' z η) := by
  have ht : Tendsto (fun q : ℝ × E ↦ (q.2, q.1 • η)) (𝓝 (1, x)) (𝓝 (x, η)) := by
    have hc : Continuous (fun q : ℝ × E ↦ (q.2, q.1 • η)) :=
      continuous_snd.prodMk (continuous_fst.smul continuous_const)
    simpa only [ContinuousAt, one_smul] using hc.continuousAt (x := ((1 : ℝ), x))
  have he := h.comp_tendsto ht
  rw [nhds_prod_eq] at he
  have he' := he.curry
  have hz := h.comp_tendsto (continuousAt_id.prodMk (continuousAt_const (y := η)))
  filter_upwards [hh, he'] with t hhom heq
  filter_upwards [hhom, heq, hz] with z hhom heq hz
  exact heq.trans (hhom.trans (congrArg (t * ·) hz.symm))

/-- Frequency support is preserved by both adjoint branch operations and the
first output derivative. This closes the supported admissibility induction.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjoint_branches_frequency_support {S : E → E → ℝ}
    {C : FullAmplitude n r} {F : Set E}
    (hF : ∀ x y η, η ∉ F → C x y η = 0) (i : Fin n) :
    (∀ x y η, η ∉ F → adjointTransferRemainder S i C x y η = 0) ∧
    (∀ j x y η, η ∉ F → adjointTransferDatum S i j C x y η = 0) ∧
    (∀ x y η, η ∉ F → reverseFirstOutputAmplitude C i x y η = 0) := by
  have hd (j x y η) (hη : η ∉ F) : adjointTransferDatum S i j C x y η = 0 := by
    simp [adjointTransferDatum, hF x y η hη]
  refine ⟨?_, hd, ?_⟩
  · intro x y η hη
    have hc (x y) := hF x y η hη
    have hp (j x y) := hd j x y η hη
    simp [adjointTransferRemainder, hc, hp, partialDeriv]
  · intro x y η hη
    have hc (x y) := hF x y η hη
    simp [reverseFirstOutputAmplitude, hc, partialDeriv]

/-- The literal reverse integral is unchanged by phase agreement on its
amplitude support; the normalization and both positions are untouched.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverseGraphOperator_phase_congr (S S' : E → E → ℝ) (C : FullAmplitude n r)
    (h : ∀ x y η, C x y η ≠ 0 → S' x η = S x η)
    (v : E → Fin r → ℂ) : reverseGraphOperator S' C v = reverseGraphOperator S C v := by
  funext y
  unfold reverseGraphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hc : C x y η = 0
  · simp only [hc, Matrix.zero_mulVec, smul_zero]
  · rw [graphOscillation, graphOscillation, h x y η hc]

end JanetCartan.FourierIntegral.SupportedSobolev
