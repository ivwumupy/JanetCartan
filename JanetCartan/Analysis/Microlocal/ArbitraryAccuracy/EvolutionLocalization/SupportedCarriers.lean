module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers.Locality

/-!
# Supported elapsed carriers and exact phase locality

The carrier and domain inputs for
`FiniteChain.Graph.exists_graph_factor_sobolev_bound_of_primitive_grades`
are constructed from the actual masks, multiplier and original spatial
symbol support. The common domain uses one bounded elapsed interval.

`exists_elapsedPhase_extension_preserving_localization` resolves the primitive
theorem's global-continuity requirement: use its smooth physical extension
and `WholeImageGeometry.normalizedPhase` of that same extension. The separate
scaling and germ lemmas preserve the original chart controls and phase grades.
`elapsed_summedJointKernel_test_phase_congr` and
`elapsed_regularizationLimit_phase_congr` remove the extension from both
identifications of the resulting operator, in either orientation.

The geometric inputs below are the original two-time chart buffers and
symbol support. Quantitative phase/chart grades and the final Sobolev estimate
remain the parent construction's obligations; no such estimate is a premise
or a conclusion here. Sources: `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FourierIntegral.WholeImageGeometry
open FiniteChain.Graph FiniteChain.Graph.KernelLimits

variable {d q : ℕ}

/-- Construct one smooth auxiliary physical phase preserving both literal
orientations, every regularized joint kernel, every localized composition,
and the original full graph. Its compact physical carriers include all low
and high shells; normalized germ agreement includes the mixed chart points.
The original two-time producer supplies `hbuffer` and `hscaled`, and the
original symbol supplies `hb`. No global regularity at spatial frequency zero
or desired graph bound is assumed (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedPhase_extension_preserving_localization
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (Δ : ℝ)
    {W : Set (SymbolBudgets.TwoTimePoint d)} (hW : IsOpen W)
    (hΨ : ContDiffOn ℝ ∞ (SymbolBudgets.jointPhase Ψ) W)
    (χout χsource β : Euclidean (d + 1) → ℂ) (hout : HasCompactSupport χout)
    {F : Set (Euclidean d)} (hF : IsClosed F)
    (hb : ∀ t s y η, η ∉ F → b t s y η = 0)
    (hbuffer : ∀ r ∈ Icc 0 Δ, ∀ u ∈ tsupport χout,
      ∀ ξ ∈ elapsedFrequencyCarrier β F, elapsedPhasePoint r (u, ξ) ∈ W)
    (ρ : ℝ) {T : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hT : IsCompact T)
    (hscaled : ∀ p ∈ T, (p.1, ρ • p.2) ∈ elapsedCommonPhaseDomain Δ W)
    {r : ℝ} (hr : r ∈ Icc 0 Δ) :
    ∃ (S' : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
      (V : Set (Euclidean (d + 1) × Euclidean (d + 1))),
      ContDiff ℝ ∞ (Function.uncurry S') ∧ IsOpen V ∧
      V ⊆ elapsedCommonPhaseDomain Δ W ∧
      (∀ low j, IsCompact (elapsedPhysicalPhaseCarrier χout β F low j) ∧
        elapsedPhysicalPhaseCarrier χout β F low j ⊆ V) ∧
      (∀ p ∈ V, Function.uncurry S' =ᶠ[𝓝 p] Function.uncurry (elapsedPhase Ψ r)) ∧
      (∀ p ∈ T, Function.uncurry (normalizedPhase ρ S') =ᶠ[𝓝 p]
        Function.uncurry (normalizedPhase ρ (elapsedPhase Ψ r))) ∧
      FullLowBounds.fullGraphOperator S' (elapsedAmplitude b χout χsource β r) =
        elapsedGraph Ψ b χout χsource β r ∧
      FullLowBounds.reverseFullGraphOperator S' (elapsedAmplitude b χout χsource β r) =
        FullLowBounds.reverseFullGraphOperator (elapsedPhase Ψ r)
          (elapsedAmplitude b χout χsource β r) ∧
      ∀ (backward : Bool) (mi mo : LocalizerSymbol (d + 1))
        (χA χo : Euclidean (d + 1) → ℝ),
        (∀ x y, regularizedJointKernel backward S' (elapsedAmplitude b χout χsource β r)
          mi mo χA χo x y =
          regularizedJointKernel backward (elapsedPhase Ψ r)
            (elapsedAmplitude b χout χsource β r) mi mo χA χo x y) ∧
        ∀ f : Euclidean (d + 1) → Fin q → ℂ,
          leftLocalizer 1 (fun z => χo z.2 * (1 - mo z))
            ((if backward then reverseGraphOperator else graphOperator) S'
              (fun u z ξ => (χA ξ : ℂ) • elapsedAmplitude b χout χsource β r u z ξ)
              (rightLocalizer 1 mi f)) =
          leftLocalizer 1 (fun z => χo z.2 * (1 - mo z))
            ((if backward then reverseGraphOperator else graphOperator) (elapsedPhase Ψ r)
              (fun u z ξ => (χA ξ : ℂ) • elapsedAmplitude b χout χsource β r u z ξ)
              (rightLocalizer 1 mi f)) := by
  obtain ⟨S', V, hs, hV, hVU, hphysical, hscaledV, he, hKV⟩ :=
    exists_supported_elapsedPhase_extension Ψ Δ hW hΨ hout β hF hbuffer ρ hT hscaled hr
  have hvalue u (hu : u ∈ tsupport χout) ξ (hξ : ξ ∈ elapsedFrequencyCarrier β F) :
      S' u ξ = elapsedPhase Ψ r u ξ :=
    (he (u, ξ) (hphysical ⟨hu, hξ⟩)).eq_of_nhds
  have hgraph := elapsed_fullGraph_phase_congr Ψ b χout χsource β hF hb r S' hvalue
  refine ⟨S', V, hs, hV, hVU,
    fun low j => ⟨isCompact_elapsedPhysicalPhaseCarrier hout β hF low j, hKV low j⟩,
    he, ?_, hgraph.1, hgraph.2, ?_⟩
  · intro p hp
    exact normalized_supportedPhaseExtension_eventuallyEq ρ (he _ (hscaledV p hp))
  · intro backward mi mo χA χo
    exact ⟨elapsed_regularizedJointKernel_phase_congr Ψ b χout χsource β hF hb r S' hvalue
      backward mi mo χA χo,
      elapsed_regularizedComposition_phase_congr Ψ b χout χsource β hF hb r S' hvalue
        backward mi mo χA χo⟩

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
