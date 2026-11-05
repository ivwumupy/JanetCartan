module

public import JanetCartan.Analysis.Microlocal.SelectedSectorProtection.InitializedApplication
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SourceGeometry

/-!
# The same selected-sector conclusion with even witnesses

This is an output proposition, never a construction hypothesis. It exposes
physical covector evenness on the SAME existential mask witnesses as every
original support, propagation, grade and phase-gap conclusion. Forgetting
only this additional conclusion recovers `SelectedSectorNestedMaskConclusion`.
Consumers: the complete physical residual's `hieven` and `hoeven`, and the
real paired local factor of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open SelectedSectorProtection
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open ProtectedMasks ProtectedMasks.ConicInterior ProtectedFlow EvolutionIntegratedLocalization FiniteChain.Graph
open JanetCartan.Localization

variable {d : ℕ} {M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- All original selected mask conclusions, with evenness on their actual
witnesses. This output is constructed from the original protected geometry;
no independent choice of masks is equated to it
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
def SelectedSectorEvenNestedMaskConclusion
    {Ω : Set E} {x : E} {RQ : ℝ}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    (χ₂ : E → ℝ) (Ksource : Set E) (V : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set Z)
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP) : Prop :=
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let W := closedBall x RQ
    let S := tsupport χ₂ ×ˢ Ksource
    let Δ := 6 * f.physicalRadius
    let h : J → Z → ℝ := fun p ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
    let irad : ((j : J) × Fin (n j)) → Fin (d+1) := fun k ↦ i k.1
    let hrad : ((j : J) × Fin (n j)) → Z → ℝ := fun k ↦ h k.1
    let Φrad : ((j : J) × Fin (n j)) → Z × ℝ → Z := fun k ↦
      radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
    let Ur : ((j : J) × Fin (n j)) → Set Z := fun k ↦ Urad k.1 k.2
    let Kr : ((j : J) × Fin (n j)) → Set Z := fun k ↦
      rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' ''
        closedBall (z k.1) (f.chart k.1).rootRadius
    let Ractual : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W
      (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
    let Runit : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
    ∃ (Gext : J → TwoTimePoint (Euclidean d) → ℝ)
      (m : Fin (N + 1) → LocalizerSymbol (d + 1)),
      (∀ k y ξ, m k (y, -ξ) = m k (y, ξ)) ∧
      (∀ j, Continuous (Gext j) ∧ ContDiffOn ℝ ∞ (Gext j) {q | q.2.2.2 ≠ 0} ∧
        (∀ (q : TwoTimePoint (Euclidean d)) (s : ℝ), 0 < s →
          Gext j (q.1, (q.2.1, (q.2.2.1, s • q.2.2.2))) = s * Gext j q) ∧
        ∀ q ∈ ConicPhase.domain (ℓ j) (closedBall ((z j).1, z j) (2 * (f.chart j).maskRadius)),
          Gext j =ᶠ[𝓝 q] ConicPhase.phase (ℓ j) (Cphase j)) ∧
      (∀ k, IsBufferedLocalizer (m k)
        (reachableAt Ractual S k.val)
        (physicalProtectedRegion Γ)) ∧
      IsBufferedLocalizer (m 0) S V ∧
      cthickening θ (tsupport (m 0)) ⊆ V ∧
      (∀ k, cthickening θ (reachableAt
        Ractual S k.val) ⊆
          interior {p | m k p = 1}) ∧
      (∀ k, cthickening θ (tsupport (m k)) ⊆
        (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
          physicalProtectedRegion Γ) ∧
      (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
      (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
        p = q ∨ Ractual p q →
          closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
      (∀ k j, IsBufferedLocalizer
        (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
          Ractual S k.val)
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
      (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
        closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
      (∀ k j l p, ‖iteratedFDeriv ℝ l
        (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
      (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
        p = q ∨ Runit p q →
            closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
      (∀ (k : Fin N) (χ₂ χ₃ : Euclidean (d + 1) → ℝ),
        EqOn χ₃ 1 (tsupport χ₂) →
        ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
          sourceRecutRelation χ₂ Ractual p q →
            χ₃ p.1 = 1 ∧ closedBall q θ ⊆ interior {q | m k.succ q = 1}) ∧
      ∀ (k : Fin N) (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
      ∀ (x y : Euclidean (d + 1)) (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
        r' ∈ Icc 0 Δ → r' ≤ (f.chart j).maskRadius →
        p.1.1 0 ∈ closedBall (z j).1 ((f.chart j).maskRadius / 2) →
        spatialPart p.1.1 ∈ closedBall (z j).2.1 ((f.chart j).maskRadius / 2) →
        spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2
          ((f.chart j).maskRadius / 2) (aPhase j) (bPhase j) →
        (y, p.2.2.1) ∈ cthickening (θ / 2)
          (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
        (x, p.2.2.2) ∈ tsupport
          (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (r', w)) p)) ∧
        δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
            (SymbolBudgets.normalizedTwoTimePhase Rf
              (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (r', w)) p) ∧
        fderiv ℝ (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ≠ 0 ∧
        fderiv ℝ (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (0, w)) p ≠ 0 ∧
        fderiv ℝ (jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ≠ 0 ∧
        fderiv ℝ (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (0, w)) p ≠ 0


/-- Forgetting evenness recovers the entire existing selected-sector
conclusion on the SAME parameters and witnesses
(`app:ch_regular:lem:finite-chain`). -/
theorem selectedSectorNestedMaskConclusion_of_even
    {Ω : Set E} {x : E} {RQ : ℝ}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    (χ₂ : E → ℝ) (Ksource : Set E) (V : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set Z)
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP)
    (heven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase) :
    SelectedSectorNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  dsimp only [SelectedSectorEvenNestedMaskConclusion, SelectedSectorNestedMaskConclusion] at heven ⊢
  obtain ⟨Gext, m, _, hmask⟩ := heven
  exact ⟨Gext, m, hmask⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
