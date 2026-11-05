module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FactorWeights

/-!
# Complete images of the four retained factor weights

Connect the actual supports from `FactorWeights` to the actual retained flow,
including every intermediate time and both retarded orientations. The finite
chain statements consume the geometric rectangles constructed in
`FactorRectangles`, and feed the source-product buffer in `SignedProtection`.
This is the factor-relation step of `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover FiniteChain.Retarded

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace CanonicalFactorWeights

variable {c : CanonicalPhase V} {ρ : ℝ} (w : CanonicalFactorWeights c ρ)

/-- The physical image of the complete relation on the actual closed supports
of the four weights. No invariance or protection condition is included in this
definition (`app:ch_regular:thm:no-return`). -/
def physicalRelation {H : HomogeneousSymbol (Euclidean n)}
    (Φ : HamiltonFlow H V) (backward : Bool)
    (z v : Euclidean n × Euclidean n) : Prop :=
  ∃ p ∈ w.sourceProduct, ∃ q ∈ w.sourceProduct,
    canonicalState Φ p = z ∧ canonicalState Φ q = v ∧ CompleteRelation backward p q

/-- Every complete retarded image of the actual source product admits an
entire buffered physical segment. The same radius protects both orientations,
all source shoulders and all intermediate times. The rectangle hypotheses
are supplied by `ComparisonChart.exists_factor_rectangles`
(`app:ch_regular:thm:no-return`). -/
theorem completeImage_has_buffered_segments
    {H : HomogeneousSymbol (Euclidean n)} {Φ : HamiltonFlow H V}
    (C : ProjectionChart Φ) (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε)
    {W : Set (Euclidean n)}
    (hchart : MapsTo canonicalFlowLift (closedBall c (2 * ρ)) C.source)
    (hbuffer : ∀ z ∈ closedBall c (2 * ρ), closedBall (canonicalState Φ z).1 ε ⊆ W)
    {K : Set (CanonicalPhase V)} (hK : K ⊆ w.sourceProduct)
    {backward : Bool} {q : CanonicalPhase V}
    (hq : q ∈ completeImage backward w.physicalSupport K) :
    ∃ p ∈ K,
      (canonicalState Φ p = canonicalState Φ q ∨
        CompleteCharacteristicSegment H W (canonicalState Φ p) (canonicalState Φ q)) ∧
      ∀ t ∈ Icc (min p.1.1 q.1.1) (max p.1.1 q.1.1),
        closedBall (canonicalState Φ ((t, p.1.2), p.2)).1 ε ⊆ W := by
  have hqrect := w.sourceProduct_subset hρ.le (w.completeImage_subset backward hK hq)
  obtain ⟨_, p, hp, hrel⟩ := hq
  have hprect := w.sourceProduct_subset hρ.le (hK hp)
  have hsub : closedBall c ρ ⊆ closedBall c (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨p, hp, ?_, ?_⟩
  · exact completeRelation_maps_to_characteristicSegment Φ
      (fun z hz ↦ C.source_admissible _ (hchart hz))
      (fun z hz ↦ hbuffer z hz (mem_closedBall_self hε.le))
      (hsub hprect) (hsub hqrect) hrel
  · intro t ht
    exact hbuffer _ (hsub (canonical_time_segment_mem_closedBall hprect hqrect ht))

/-- The relation of the four actual weights is diagonal or a complete
characteristic segment of the same retained Hamilton flow
(`app:ch_regular:thm:no-return`). -/
theorem physicalRelation_is_characteristic_step
    {H : HomogeneousSymbol (Euclidean n)} {Φ : HamiltonFlow H V}
    (C : ProjectionChart Φ) (hρ : 0 < ρ)
    {W : Set (Euclidean n)}
    (hchart : MapsTo canonicalFlowLift (closedBall c (2 * ρ)) C.source)
    (hphysical : ∀ z ∈ closedBall c (2 * ρ), (canonicalState Φ z).1 ∈ W)
    {backward : Bool} {z v : Euclidean n × Euclidean n}
    (hrel : w.physicalRelation Φ backward z v) :
    PositiveConicChainStep (CompleteCharacteristicSegment H W) z v := by
  obtain ⟨p, hp, q, hq, rfl, rfl, hrel⟩ := hrel
  have hsub := (w.sourceProduct_subset hρ.le).trans
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ))
  exact completeRelation_maps_to_characteristicSegment Φ
    (fun _ hz ↦ C.source_admissible _ (hchart hz)) hphysical (hsub hp) (hsub hq) hrel

end CanonicalFactorWeights

/-- A chain assembled from either orientation of any retained weighted
factor is a chain of the actual complete characteristic segments. No bound
on chain length is used (`app:ch_regular:thm:no-return`). -/
theorem weightedFactor_chain_is_characteristic_chain {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)} {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart H (g i))
    (c : (i : I) → CanonicalPhase (g i).tangentSpace) {ρ : I → ℝ}
    (w : (i : I) → CanonicalFactorWeights (c i) (ρ i)) (hρ : ∀ i, 0 < ρ i)
    {W : Set (Euclidean n)}
    (hchart : ∀ i, MapsTo canonicalFlowLift (closedBall (c i) (2 * ρ i)) (C i).chart.source)
    (hphysical : ∀ i, ∀ z ∈ closedBall (c i) (2 * ρ i),
      (canonicalState (C i).flow z).1 ∈ W)
    {z v : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain
      (fun z v ↦ ∃ i backward, (w i).physicalRelation (C i).flow backward z v) z v k) :
    PositiveConicChain (CompleteCharacteristicSegment H W) z v k := by
  induction hchain with
  | refl z => exact .refl z
  | @tail z y v k hstep hrest ih =>
    apply PositiveConicChain.tail ?_ ih
    rcases hstep with hdiag | ⟨i, backward, hrel⟩
    · exact Or.inl hdiag
    · exact (w i).physicalRelation_is_characteristic_step (C i).chart
        (hρ i) (hchart i) (hphysical i) hrel

/-- Elliptic sources have only identity images under every finite chain of
the actual weighted factors, including arbitrary choices of orientation
(`app:ch_regular:thm:no-return`). -/
theorem elliptic_weightedFactor_chain_eq {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)} {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart H (g i))
    (c : (i : I) → CanonicalPhase (g i).tangentSpace) {ρ : I → ℝ}
    (w : (i : I) → CanonicalFactorWeights (c i) (ρ i)) (hρ : ∀ i, 0 < ρ i)
    {W : Set (Euclidean n)}
    (hchart : ∀ i, MapsTo canonicalFlowLift (closedBall (c i) (2 * ρ i)) (C i).chart.source)
    (hphysical : ∀ i, ∀ z ∈ closedBall (c i) (2 * ρ i),
      (canonicalState (C i).flow z).1 ∈ W)
    {z v : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain
      (fun z v ↦ ∃ i backward, (w i).physicalRelation (C i).flow backward z v) z v k)
    (hz : H.h z ≠ 0) : z = v :=
  elliptic_completeCharacteristic_chain_eq
    (weightedFactor_chain_is_characteristic_chain C c w hρ hchart hphysical hchain) hz

namespace PhaseCover.ComparisonChart

/-- Construct the four weights on a finite cover of every retained chart's
complete compact canonical source. Their source and target plateaus cover
the entire product, so no source point is dropped by localization. The same
width works across all charts for this current symbol. Uniform selection in
the current symbol remains separate (`app:ch_regular:thm:no-return`). -/
theorem exists_weighted_factor_rectangles {I : Type*} [Finite I]
    {H : HomogeneousSymbol (Euclidean n)} {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart H (g i))
    {r τ : ℝ} (hr : 0 < r) (hradius : ∀ i, r ≤ 2 * (g i).radius) (hτ : 0 < τ) :
    ∃ ρ > (0 : ℝ), ρ < τ ∧ ∀ i,
      ∃ (centers : Finset ((C i).canonicalSource r))
        (w : (q : centers) → CanonicalFactorWeights q.1.1 ρ),
        (∀ z ∈ (C i).canonicalSource r, ∃ q : centers,
          (w q).base 0 z.1 * (w q).frequency z.2 = 1 ∧
          (w q).base 1 z.1 * (w q).frequency z.2 = 1) ∧
        (∀ q : centers, MapsTo canonicalFlowLift (closedBall q.1.1 (2 * ρ))
          (C i).chart.source) ∧
        ∃ εx > (0 : ℝ), ∀ q : centers, ∀ z ∈ closedBall q.1.1 (2 * ρ),
          closedBall (canonicalState (C i).flow z).1 εx ⊆ ball 0 (2 * r) := by
  classical
  obtain ⟨ρ, hρ, hρτ, hrect⟩ := exists_common_width_factor_rectangles C hr hradius hτ
  refine ⟨ρ, hρ, hρτ, ?_⟩
  intro i
  obtain ⟨centers, hcover, hchart, ⟨εx, hεx, hbuffer⟩, _hmasks⟩ := hrect i
  obtain ⟨w, hw⟩ := exists_canonicalFactorWeights_cover centers hρ hcover
  exact ⟨centers, w, hw, fun q z hz ↦ (hchart q.1 z hz).1,
    εx, hεx, fun q ↦ hbuffer q.1⟩

end PhaseCover.ComparisonChart

end JanetCartan.ProtectedFlow
