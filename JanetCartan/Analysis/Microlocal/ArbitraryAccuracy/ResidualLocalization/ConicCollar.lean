module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.FiniteFamilyCollar
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Normalized

/-!
# Frequency-independent collars for the original conic residual phase

The smooth supported extension is used only to construct the collar. Its
open germ-equality set transfers the gaps to the original conic phase.
The actual conic extension's proved homogeneity removes radial normalization,
so the same domains, collar, positive constants and profiles work for every
positive physical frequency. Negative elapsed times impose no gradient
condition. The physical kernel still integrates on the original half-space.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph EvolutionIntegratedLocalization JanetCartan.Localization
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables E
set_option maxHeartbeats 800000

/-- Derive the exact normalized-phase collar interface of
`exists_directResidual_integral_fourier_bound_of_primitive_grades` for the
original conic extension. Its homogeneity is proved by
`normalizedTwoTimePhase_curriedExtend`; the supported germ input is the output
of `exists_supported_twoTimePhase_extension` on the closed physical carrier.
No gradient gap or successful localized estimate is a premise. The buffered
chart and mask hypotheses remain geometric inputs from `ResidualCoordinates`
and the protected-mask construction (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_finiteFamily_conic_residual_collar
    {α ι κ : Type*} [Finite α] [TopologicalSpace α] [DiscreteTopology α] [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (bases : α → Set (E × E)) (carrier : α → Set V)
    (mi mo : α → LocalizerSymbol (d + 1))
    (hbases : ∀ a, IsCompact (bases a)) (hcarrier : ∀ a, IsCompact (carrier a))
    (h : α → RootState (Euclidean d) → ℝ)
    (Φ : α → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : α → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (Ψ : α → TwoTimePhase d)
    (R : α → Set (E × E))
    (ℓ : α → Euclidean d →L[ℝ] ℝ)
    (F : α → TwoTimePoint (Euclidean d) → ℝ) :
    let K := elapsedFiniteFamilyCarrier bases carrier mi mo
    ∀ (_hΨ : ∀ t, ContDiff ℝ ∞ (SymbolBudgets.jointPhase (Ψ t)))
    (_hC : ∀ t, (C t : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ t))
    (_hdiag : ∀ t, tsupport (mi t) ⊆ interior {p | mo t p = 1})
    (_hflow : ∀ backward, ∀ t ∈ K, 0 < t.2.1 → ∀ a ∈ tsupport (mi t.1.1), ∀ b ∈ R t.1.1,
      zeroEnergyFlowRelation backward (h t.1.1) (Φ t.1.1) t.2.1 a b →
        b ∈ interior {p | mo t.1.1 p = 1})
    (_hR : ∀ t ∈ K, (t.1.2.1, t.2.2.2.2.2) ∈ R t.1.1)
    (_hqB : ∀ t ∈ K, elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1.1).target)
    (_hi : ∀ t ∈ K,
      Φ t.1.1 (((C t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2, 0) =
        ((C t.1.1).symm (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1)).2)
    (_hphaseB : ∀ t ∈ K, HasFDerivAt (twoTimePhase (C t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (C t.1.1)
        (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint 0 t.2.2.1.1 t.2.2.2.1))
    (_hqI : ∀ t ∈ K, 0 < t.2.1 →
      elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1 ∈ (C t.1.1).target)
    (_hclock : ∀ t ∈ K, 0 < t.2.1 →
      (twoTimeState (Φ t.1.1) ((C t.1.1).symm
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))).1 = t.2.2.1.1 0)
    (_hphaseI : ∀ t ∈ K, 0 < t.2.1 → HasFDerivAt (twoTimePhase (C t.1.1))
      (twoTimePhaseDifferential (h t.1.1) (Φ t.1.1) (C t.1.1)
        (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
      (elapsedChartPoint t.2.1 t.2.2.1.1 t.2.2.2.1))
    (_hGermB : ∀ t ∈ K, SymbolBudgets.jointPhase (Ψ t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates (0, t.2.2))] SymbolBudgets.jointPhase (chartPhase (C t.1.1)))
    (_hGermI : ∀ t ∈ K, 0 < t.2.1 → SymbolBudgets.jointPhase (Ψ t.1.1) =ᶠ[𝓝
      (elapsedJointCoordinates t.2)] SymbolBudgets.jointPhase (chartPhase (C t.1.1)))
    (_hsupported : ∀ t ∈ K, 0 ≤ t.2.1 →
      SymbolBudgets.jointPhase (Ψ t.1.1) =ᶠ[𝓝 (elapsedJointCoordinates t.2)]
        SymbolBudgets.jointPhase (ConicPhase.curriedExtend (ℓ t.1.1) (F t.1.1))),
    ∃ (χ : Bool → V → ℂ) (UT UI : Bool → α × (E × E) → Set V)
      (ε δT δI G : ℝ) (H : ℕ → ℝ),
      0 < ε ∧ 0 < δT ∧ 0 < δI ∧ (∀ j, 0 ≤ H j) ∧
      ∀ (ρ : ℝ), 0 < ρ → ∀ backward,
      ContDiff ℝ ∞ (χ backward) ∧
      (∀ t, IsOpen (UT backward t)) ∧ (∀ t, IsOpen (UI backward t)) ∧
      (∀ p, |p.1| < ε → χ backward p = 1) ∧
      (∀ a x y, (x, y) ∈ bases a →
        elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y ∩ tsupport (χ backward) ⊆
          UT backward (a, x, y)) ∧
      (∀ a x y, (x, y) ∈ bases a →
        (elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y ∩ tsupport (1 - χ backward)) ∩
          {p | 0 < p.1} ⊆ UI backward (a, x, y)) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward t →
        δT ≤ phaseGradientSquare eT
          (fun w ↦ jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
            (ConicPhase.curriedExtend (ℓ t.1) (F t.1))) t.2.1 t.2.2 (r, w)) p) ∧
      (∀ t r, 0 ≤ r → ∀ p, (r, p) ∈ UT backward t →
        ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
            (ConicPhase.curriedExtend (ℓ t.1) (F t.1))) t.2.1 t.2.2) (r, p)‖ ≤ G) ∧
      (∀ t p, p ∈ UI backward t ∩ {p | 0 < p.1} →
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
            (ConicPhase.curriedExtend (ℓ t.1) (F t.1))) t.2.1 t.2.2) p) ∧
      (∀ t p, p ∈ UI backward t ∩ {p | 0 < p.1} →
        ‖fderiv ℝ (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
            (ConicPhase.curriedExtend (ℓ t.1) (F t.1))) t.2.1 t.2.2) p‖ ≤ G) ∧
      (∀ a x y, (x, y) ∈ bases a →
        ∀ p ∈ elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y, ∀ j,
          ‖iteratedFDeriv ℝ j (χ backward) p‖ ≤ H j) := by
  classical
  intro K hΨ hC hdiag hflow hR hqB hi hphaseB hqI hclock hphaseI hGermB hGermI hsupported
  obtain ⟨χ, UT, UI, ε, δT, δI, G, H, hε, hδT, hδI, hH, hdata⟩ :=
    exists_finiteFamily_buffered_residual_collar eT eI bases carrier mi mo hbases hcarrier
      h Φ C Ψ R hΨ hC hdiag hflow hR hqB hi hphaseB hqI hclock hphaseI hGermB hGermI
  let Ω (t : α × (E × E)) : Set V := {p |
    SymbolBudgets.jointPhase (Ψ t.1) =ᶠ[𝓝 (elapsedJointCoordinates p)]
      SymbolBudgets.jointPhase (ConicPhase.curriedExtend (ℓ t.1) (F t.1))}
  have hΩ t : IsOpen (Ω t) := isOpen_setOfPred_eventually_nhds.preimage elapsedJointCoordinates.continuous
  let U (backward : Bool) (t : α × (E × E)) := UT backward t ∩ (Ω t ∪ {p : V | p.1 < 0})
  let W (backward : Bool) (t : α × (E × E)) := UI backward t ∩ Ω t
  have hmem a x y (hxy : (x, y) ∈ bases a) p
      (hp : p ∈ elapsedOutputJetCarrier (carrier a) (mi a) (mo a) x y)
      (hr : 0 ≤ p.1) : p ∈ Ω (a, x, y) := hsupported ((a, x, y), p) ⟨hxy, hp⟩ hr
  have he backward t p (hp : p ∈ Ω t) :
      jointElapsedPhase backward (Ψ t.1) t.2.1 t.2.2 =ᶠ[𝓝 p]
        jointElapsedPhase backward (ConicPhase.curriedExtend (ℓ t.1) (F t.1)) t.2.1 t.2.2 :=
    jointElapsedPhase_eventuallyEq_of_twoTimePhase backward _ _ _ _ _ hp
  refine ⟨χ, U, W, ε, δT, δI, G, H, hε, hδT, hδI, hH, ?_⟩
  intro ρ hρ backward
  obtain ⟨hχ, hUT, hUI, hχone, hχT, hχI, hgapT, hupperT, hgapI, hupperI, hχbound⟩ := hdata backward
  refine ⟨hχ, fun t ↦ (hUT t).inter ((hΩ t).union (isOpen_lt continuous_fst continuous_const)),
    fun t ↦ (hUI t).inter (hΩ t), hχone, ?_, ?_, ?_, ?_, ?_, ?_, hχbound⟩
  · intro a x y hxy p hp
    refine ⟨hχT a x y hxy hp, ?_⟩
    by_cases hr : 0 ≤ p.1
    · exact Or.inl (hmem a x y hxy p hp.1 hr)
    · exact Or.inr (lt_of_not_ge hr)
  · intro a x y hxy p hp
    exact ⟨hχI a x y hxy hp, hmem a x y hxy p hp.1.1 (le_of_lt hp.2)⟩
  · intro t r hr p hp
    have hΩp : (r, p) ∈ Ω t := hp.2.resolve_right (not_lt_of_ge hr)
    rw [ConicPhase.normalizedTwoTimePhase_curriedExtend _ _ hρ]
    have he' := fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ backward
      (ConicPhase.curriedExtend (ℓ t.1) (F t.1)) (Ψ t.1) t.2.1 t.2.2 r p hΩp
    simpa only [phaseGradientSquare, he'] using hgapT t r hr p hp.1
  · intro t r hr p hp
    have hΩp : (r, p) ∈ Ω t := hp.2.resolve_right (not_lt_of_ge hr)
    rw [ConicPhase.normalizedTwoTimePhase_curriedExtend _ _ hρ, ← (he backward t (r, p) hΩp).fderiv_eq]
    exact hupperT t r hr p hp.1
  · intro t p hp
    rw [ConicPhase.normalizedTwoTimePhase_curriedExtend _ _ hρ]
    simpa only [phaseGradientSquare, (he backward t p hp.1.2).fderiv_eq] using
      hgapI t p ⟨hp.1.1, hp.2⟩
  · intro t p hp
    rw [ConicPhase.normalizedTwoTimePhase_curriedExtend _ _ hρ, ← (he backward t p hp.1.2).fderiv_eq]
    exact hupperI t p ⟨hp.1.1, hp.2⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
