module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.Domains
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Phase

/-!
# A globally continuous auxiliary phase for the same elapsed operator

The primitive graph theorem requires global continuity of its physical phase.
We construct a smooth extension on the closed physical support together with
the dilated compact chart carrier. Its normalized phase satisfies the scaling
identity everywhere by definition; its jets agree with the original normalized
phase near the chart carrier. No global homogeneity of the extension is used.
The original phase is never required to be smooth at spatial covector zero.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FourierIntegral.WholeImageGeometry

variable {d : ℕ}

/-- Construct a smooth extension preserving the entire physical frequency
support and the normalized chart's mixed points at physical scale. The
physical buffer comes from the original symbol/multiplier chart; `hscaled`
comes from its conic chart buffer, and `T` is supplied by
`elapsedMixedPhaseCarrier`. The returned open set is an agreement domain
on which all original physical derivative bounds transfer unchanged.
Consumer: global continuity, local regularity and chart locality in
`exists_graph_factor_sobolev_bound_of_primitive_grades`
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_supported_elapsedPhase_extension
    (Ψ : TwoTimePhase d) (Δ : ℝ)
    {W : Set (SymbolBudgets.TwoTimePoint d)} (hW : IsOpen W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    {χout : Euclidean (d + 1) → ℂ} (hout : HasCompactSupport χout)
    (β : Euclidean (d + 1) → ℂ) {F : Set (Euclidean d)} (hF : IsClosed F)
    (hbuffer : ∀ r ∈ Icc 0 Δ, ∀ u ∈ tsupport χout,
      ∀ ξ ∈ elapsedFrequencyCarrier β F, elapsedPhasePoint r (u, ξ) ∈ W)
    (ρ : ℝ) {T : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hT : IsCompact T)
    (hscaled : ∀ p ∈ T, (p.1, ρ • p.2) ∈ elapsedCommonPhaseDomain Δ W)
    {r : ℝ} (hr : r ∈ Icc 0 Δ) :
    ∃ (S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
      (V : Set (Euclidean (d + 1) × Euclidean (d + 1))),
      ContDiff ℝ ∞ (Function.uncurry S') ∧ IsOpen V ∧
      V ⊆ elapsedCommonPhaseDomain Δ W ∧
      tsupport χout ×ˢ elapsedFrequencyCarrier β F ⊆ V ∧
      (∀ p ∈ T, (p.1, ρ • p.2) ∈ V) ∧
      (∀ p ∈ V, Function.uncurry S' =ᶠ[𝓝 p] Function.uncurry (elapsedPhase Ψ r)) ∧
      ∀ low j, elapsedPhysicalPhaseCarrier χout β F low j ⊆ V := by
  let K := tsupport χout ×ˢ elapsedFrequencyCarrier β F
  let Dρ := fun p : Euclidean (d + 1) × Euclidean (d + 1) => (p.1, ρ • p.2)
  have hDρ : Continuous Dρ := continuous_fst.prodMk (continuous_snd.const_smul ρ)
  have hK : IsClosed K := hout.isClosed.prod (isClosed_elapsedFrequencyCarrier β hF)
  have hKU : K ⊆ elapsedCommonPhaseDomain Δ W := by
    intro p hp t ht
    exact hbuffer t ht p.1 hp.1 p.2 hp.2
  have hTU : Dρ '' T ⊆ elapsedCommonPhaseDomain Δ W := by
    rintro p ⟨q, hq, rfl⟩
    exact hscaled q hq
  have hU := isOpen_elapsedCommonPhaseDomain Δ hW
  obtain ⟨S', hs, he⟩ := exists_smooth_phase_extension (elapsedPhase Ψ r)
    (hK.union (hT.image hDρ).isClosed) hU (union_subset hKU hTU)
    (contDiffOn_elapsedPhase_commonDomain Ψ Δ hW hΨ hr)
  let V := elapsedCommonPhaseDomain Δ W ∩
    interior {p | S' p.1 p.2 = elapsedPhase Ψ r p.1 p.2}
  have hKV : K ∪ Dρ '' T ⊆ V := by
    intro p hp
    exact ⟨union_subset hKU hTU hp, mem_interior_iff_mem_nhds.mpr (he p hp)⟩
  refine ⟨S', V, hs, hU.inter isOpen_interior, inter_subset_left,
    fun p hp => hKV (Or.inl hp), fun p hp => hKV (Or.inr ⟨p, hp, rfl⟩), ?_, ?_⟩
  · intro p hp
    exact mem_interior_iff_mem_nhds.mp hp.2
  · intro low j p hp
    exact hKV (Or.inl ⟨hp.1, hp.2.2⟩)

/-- Use the existing phase normalization to meet the graph theorem's exact
scaling identity globally. Homogeneity of the extension is unnecessary
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem supportedPhaseExtension_scaling {ρ : ℝ} (hρ : ρ ≠ 0)
    (S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
    (u ξ : Euclidean (d + 1)) :
    S' u (ρ • ξ) = ρ * normalizedPhase ρ S' u ξ := by
  simp [normalizedPhase, hρ]

/-- The normalized extension is globally smooth, whereas only its germ on
the supported chart is used in the estimates
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_normalized_supportedPhaseExtension (ρ : ℝ)
    {S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ}
    (hS' : ContDiff ℝ ∞ (Function.uncurry S')) :
    ContDiff ℝ ∞ (Function.uncurry (normalizedPhase ρ S')) :=
  contDiff_const.mul (hS'.comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ)))

/-- Physical germ agreement pulls back to normalized germ agreement, hence
all comparable phase jets and both chart controls can be transferred using
the existing `Comparable` locality lemmas
(`app:ch_regular:eq:joint-stationary`). -/
theorem normalized_supportedPhaseExtension_eventuallyEq (ρ : ℝ)
    {S S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ}
    {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (he : Function.uncurry S' =ᶠ[𝓝 (p.1, ρ • p.2)] Function.uncurry S) :
    Function.uncurry (normalizedPhase ρ S') =ᶠ[𝓝 p]
      Function.uncurry (normalizedPhase ρ S) := by
  have h := he.comp_tendsto
    ((continuous_fst.prodMk (continuous_snd.const_smul ρ)).tendsto p)
  filter_upwards [h] with z hz
  exact congrArg (ρ⁻¹ * ·) hz

/-- On the original homogeneous chart the normalized extension agrees with
the literal elapsed phase. Spatial homogeneity is required only on that
open chart, and is the original two-time phase producer's hypothesis
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalized_supportedPhaseExtension_eventuallyEq_elapsedPhase
    (Ψ : TwoTimePhase d) (r : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    {S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ}
    {U : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hU : IsOpen U)
    (hhom : ∀ p ∈ U,
      Ψ (p.1 0) (p.1 0 - r) (spatialPart p.1) (ρ • spatialPart p.2) =
        ρ * Ψ (p.1 0) (p.1 0 - r) (spatialPart p.1) (spatialPart p.2))
    {p : Euclidean (d + 1) × Euclidean (d + 1)} (hp : p ∈ U)
    (he : Function.uncurry S' =ᶠ[𝓝 (p.1, ρ • p.2)]
      Function.uncurry (elapsedPhase Ψ r)) :
    Function.uncurry (normalizedPhase ρ S') =ᶠ[𝓝 p]
      Function.uncurry (elapsedPhase Ψ r) := by
  apply (normalized_supportedPhaseExtension_eventuallyEq ρ he).trans
  filter_upwards [hU.mem_nhds hp] with z hz
  change ρ⁻¹ * elapsedPhase Ψ r z.1 (ρ • z.2) = elapsedPhase Ψ r z.1 z.2
  rw [elapsedPhase_smul Ψ r ρ z.1 z.2 (hhom z hz), ← mul_assoc,
    inv_mul_cancel₀ hρ, one_mul]

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
