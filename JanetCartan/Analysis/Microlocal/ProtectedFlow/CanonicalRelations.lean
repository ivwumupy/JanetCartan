module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ComparisonPropagation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Geometry

/-!
# Retarded canonical relations are complete Hamilton segments

The relation of the actual lower integral, or of its literal adjoint, transports
only the canonical time coordinate. On a complete canonical rectangle this is
an actual Hamilton segment, including every intermediate time. This connects
the retarded relation in `app:ch_regular:lem:finite-chain` to the protection
theorem `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow
open HamiltonPhase FiniteChain.Retarded

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Rearrange the canonical base and covector into the retained flow's time
and initial data (`app:ch_regular:thm:no-return`). -/
def canonicalFlowLift (p : CanonicalPhase V) : ℝ × InitialData V :=
  (p.1.1, (p.1.2, p.2))

/-- The actual physical state of a canonical point, using the retained
Hamilton flow (`app:ch_regular:thm:no-return`). -/
def canonicalState {H : HomogeneousSymbol (Euclidean n)}
    (Φ : HamiltonFlow H V) (p : CanonicalPhase V) : Euclidean n × Euclidean n :=
  (Φ.position (canonicalFlowLift p), Φ.momentum (canonicalFlowLift p))

omit [InnerProductSpace ℝ V] in
/-- Every intermediate canonical time remains in the complete closed
rectangle. Both time orientations are included
(`app:ch_regular:thm:no-return`). -/
theorem canonical_time_segment_mem_closedBall {c p q : CanonicalPhase V} {ρ t : ℝ}
    (hp : p ∈ closedBall c ρ) (hq : q ∈ closedBall c ρ)
    (ht : t ∈ Icc (min p.1.1 q.1.1) (max p.1.1 q.1.1)) :
    ((t, p.1.2), p.2) ∈ closedBall c ρ := by
  simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hp hq ⊢
  refine ⟨⟨?_, hp.1.2⟩, hp.2⟩
  have hp' := hp.1.1
  have hq' := hq.1.1
  simp only [Real.dist_eq, abs_sub_le_iff] at hp' hq'
  have ht' : t ∈ Icc (c.1.1 - ρ) (c.1.1 + ρ) := by
    apply uIcc_subset_Icc (a₁ := p.1.1) (b₁ := q.1.1) _ _ ht
    · constructor <;> linarith [hp'.1, hp'.2]
    · constructor <;> linarith [hq'.1, hq'.2]
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [ht'.1, ht'.2]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
/-- The non-diagonal branch of either retarded orientation has equal
transverse base and joint covector and zero energy
(`app:ch_regular:lem:finite-chain`). -/
theorem completeRelation_eq_or_zero_energy {backward : Bool} {p q : CanonicalPhase V}
    (h : CompleteRelation backward p q) :
    p = q ∨ (q.1.2 = p.1.2 ∧ q.2 = p.2 ∧ p.2.1 = 0) := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · exact ⟨h.2.1, Prod.ext (h.2.2.2.1.trans h.2.2.1.symm) h.2.2.2.2, h.2.2.1⟩
    · exact ⟨h.2.1.symm, Prod.ext (h.2.2.1.trans h.2.2.2.1.symm) h.2.2.2.2.symm,
        h.2.2.2.1⟩

/-- Every complete retarded relation on a retained canonical rectangle is
diagonal or an actual complete characteristic segment. The physical condition
concerns the entire rectangle, not only its endpoints. Rectangle construction
in `FactorRectangles` supplies both geometric premises
(`app:ch_regular:thm:no-return`). -/
theorem completeRelation_maps_to_characteristicSegment
    {H : HomogeneousSymbol (Euclidean n)} (Φ : HamiltonFlow H V)
    {c p q : CanonicalPhase V} {ρ : ℝ} {W : Set (Euclidean n)}
    (hadmissible : MapsTo canonicalFlowLift (closedBall c ρ) (Φ.time ×ˢ Φ.parameters))
    (hphysical : ∀ z ∈ closedBall c ρ, (canonicalState Φ z).1 ∈ W)
    (hp : p ∈ closedBall c ρ) (hq : q ∈ closedBall c ρ) {backward : Bool}
    (hrel : CompleteRelation backward p q) :
    canonicalState Φ p = canonicalState Φ q ∨
      CompleteCharacteristicSegment H W (canonicalState Φ p) (canonicalState Φ q) := by
  rcases completeRelation_eq_or_zero_energy hrel with he | ⟨hy, hη, he⟩
  · exact Or.inl (congrArg (canonicalState Φ) he)
  · right
    have hmid (t : ℝ) (ht : t ∈ Icc (min p.1.1 q.1.1) (max p.1.1 q.1.1)) :=
      canonical_time_segment_mem_closedBall hp hq ht
    have ha (t : ℝ) (ht : t ∈ Icc (min p.1.1 q.1.1) (max p.1.1 q.1.1)) :
        t ∈ Φ.time ∧ (p.1.2, p.2) ∈ Φ.parameters := hadmissible (hmid t ht)
    have hpA := hadmissible hp
    refine ⟨(Φ.energy hpA.1 hpA.2).trans he,
      (fun t ↦ Φ.position (t, (p.1.2, p.2))),
      (fun t ↦ Φ.momentum (t, (p.1.2, p.2))),
      min p.1.1 q.1.1, max p.1.1 q.1.1, p.1.1, q.1.1,
      ⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩,
      (fun t ht ↦ Φ.position_hasDerivAt (ha t ht).1 (ha t ht).2),
      (fun t ht ↦ Φ.momentum_hasDerivAt (ha t ht).1 (ha t ht).2),
      (fun t ht ↦ hphysical _ (hmid t ht)),
      (fun t ht ↦ Φ.state_mem _ (ha t ht).1 _ (ha t ht).2), rfl, ?_⟩
    simp only [canonicalState, canonicalFlowLift, hy, hη]

/-- The actual complete relation of a retained factor preserves the protected
comparison family, in both orientations. This discharges a relation premise
from the concrete canonical relation, rather than assuming invariance of the
factor (`app:ch_regular:thm:no-return`). -/
theorem completeRelation_preserves_comparisonFamily {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)}
    (hdomain : H.domain = ActualCarriers.normalizedSymbolDomain (univ : Set (Euclidean n)))
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {g : I → PhaseCover.ComparisonGeometry (Euclidean n)}
    (C : (i : I) → PhaseCover.ComparisonChart H (g i))
    {r : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    (Φ : HamiltonFlow H V) {c p q : CanonicalPhase V} {ρ : ℝ}
    (hadmissible : MapsTo canonicalFlowLift (closedBall c ρ) (Φ.time ×ˢ Φ.parameters))
    (hphysical : ∀ z ∈ closedBall c ρ, (canonicalState Φ z).1 ∈ ball 0 (2 * r))
    (hp : p ∈ closedBall c ρ) (hq : q ∈ closedBall c ρ) {backward : Bool}
    (hrel : CompleteRelation backward p q)
    (hsource : canonicalState Φ p ∈ positiveConicLift
      (PhaseCover.ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ) :
    canonicalState Φ q ∈ positiveConicLift
      (PhaseCover.ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ := by
  rcases completeRelation_maps_to_characteristicSegment Φ hadmissible hphysical hp hq hrel with h | h
  · exact h ▸ hsource
  · exact comparisonFamily_preserves_characteristicSegment hdomain hH C hradius hsource h

end JanetCartan.ProtectedFlow
