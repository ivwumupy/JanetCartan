module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FactorPropagation

/-!
# Complete relations of the fixed finite factor selection

Flatten the chart and fixed-center indices of the uniform construction. These
are the actual four-weight relations of `app:ch_regular:thm:no-return`, including
both orientations. Their entire finite chains are characteristic chains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover FiniteChain.Retarded

variable {n : ℕ} {I : Type*} {H : HomogeneousSymbol (Euclidean n)}
  {g : I → ComparisonGeometry (Euclidean n)}

/-- The union of the actual weighted relations over the fixed finite centers,
including both orientations (`app:ch_regular:thm:no-return`). -/
def selectedFactorRelation (C : (i : I) → ComparisonChart H (g i))
    {centers : (i : I) → Finset (CanonicalPhase (g i).tangentSpace)} {ρ : ℝ}
    (w : (i : I) → (q : centers i) → CanonicalFactorWeights q.1 ρ)
    (z v : Euclidean n × Euclidean n) : Prop :=
  ∃ i, ∃ q : centers i, ∃ backward, (w i q).physicalRelation (C i).flow backward z v

/-- Every chain of the actual selected factors is a complete characteristic
chain. The physical buffer and chart containment are the literal outputs of
`exists_extended_frame_uniform_cover` (`app:ch_regular:thm:no-return`). -/
theorem selectedFactor_chain_is_characteristic_chain
    (C : (i : I) → ComparisonChart H (g i))
    {centers : (i : I) → Finset (CanonicalPhase (g i).tangentSpace)} {ρ ε : ℝ}
    (w : (i : I) → (q : centers i) → CanonicalFactorWeights q.1 ρ)
    (hρ : 0 < ρ) (hε : 0 < ε) {W : Set (Euclidean n)}
    (hrect : ∀ i, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
      canonicalFlowLift z ∈ (C i).chart.source ∧
        closedBall (canonicalState (C i).flow z).1 ε ⊆ W)
    {z v : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain (selectedFactorRelation C w) z v k) :
    PositiveConicChain (CompleteCharacteristicSegment H W) z v k := by
  induction hchain with
  | refl z => exact .refl z
  | @tail z y v k hstep _ ih =>
    apply PositiveConicChain.tail ?_ ih
    rcases hstep with hdiag | ⟨i, q, backward, hrel⟩
    · exact Or.inl hdiag
    · exact (w i q).physicalRelation_is_characteristic_step (C i).chart hρ
        (fun u hu ↦ (hrect i q.1 q.2 u hu).1)
        (fun u hu ↦ (hrect i q.1 q.2 u hu).2 (mem_closedBall_self hε.le)) hrel

/-- Elliptic sources have only identity images through the actual finite
selection, for every chain length and orientation (`app:ch_regular:thm:no-return`). -/
theorem elliptic_selectedFactor_chain_eq
    (C : (i : I) → ComparisonChart H (g i))
    {centers : (i : I) → Finset (CanonicalPhase (g i).tangentSpace)} {ρ ε : ℝ}
    (w : (i : I) → (q : centers i) → CanonicalFactorWeights q.1 ρ)
    (hρ : 0 < ρ) (hε : 0 < ε) {W : Set (Euclidean n)}
    (hrect : ∀ i, ∀ q ∈ centers i, ∀ z ∈ closedBall q (2 * ρ),
      canonicalFlowLift z ∈ (C i).chart.source ∧
        closedBall (canonicalState (C i).flow z).1 ε ⊆ W)
    {z v : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain (selectedFactorRelation C w) z v k)
    (helliptic : H.h z ≠ 0) : z = v :=
  elliptic_completeCharacteristic_chain_eq
    (selectedFactor_chain_is_characteristic_chain C w hρ hε hrect hchain) helliptic

end JanetCartan.ProtectedFlow
