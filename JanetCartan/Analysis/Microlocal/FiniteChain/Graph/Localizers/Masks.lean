module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Buffered graph symbols

The mask construction for `app:ch_regular:lem:finite-chain` is uniform over a
compact family of canonical charts. The parent construction supplies the charts,
their continuity on the actual input buffer, and the image inclusion in the
output chart. In particular the image inclusion is required on the buffer,
not just on the initial compact set. This protects the input shoulders.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Topology

namespace JanetCartan.FiniteChain.Graph
open FourierIntegral

variable {n : ℕ}

/-- A physical compact set times a closed normalized covector shell, used as
the common image envelope in `app:ch_regular:lem:finite-chain`. -/
def graphChartEnvelope (R : Set (Euclidean n)) (c C : ℝ) :
    Set (Euclidean n × Euclidean n) := R ×ˢ {ξ | c ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C}

/-- Compact physical support and a uniform upper covector bound produce a
compact envelope for the complete canonical images. A positive lower endpoint
can be supplied by covector comparability (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_graphChartEnvelope {R : Set (Euclidean n)} (hR : IsCompact R)
    (c C : ℝ) : IsCompact (graphChartEnvelope R c C) := by
  apply hR.prod
  apply (isCompact_closedBall (0 : Euclidean n) C).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro ξ hξ
    simpa only [Metric.mem_closedBall, dist_zero_right] using hξ.2

/-- A smooth normalized proof symbol and its two buffers
(`app:ch_regular:lem:finite-chain`). -/
structure IsBufferedLocalizer (m : LocalizerSymbol n)
    (K O : Set (Euclidean n × Euclidean n)) : Prop where
  smooth : ContDiff ℝ ∞ m
  range : ∀ p, m p ∈ Icc (0 : ℝ) 1
  compactSupport : HasCompactSupport m
  support_subset : tsupport m ⊆ O
  plateau : K ⊆ interior {p | m p = 1}

/-- Forward and literal reverse canonical relations, with both physical bases
retained (`app:ch_regular:eq:joint-stationary`). -/
def orientedRelation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (backward : Bool) (φ : E → E → ℝ) (p q : E × E) : Prop :=
  if backward then ForwardRelation φ q.1 q.2 p.1 p.2
  else ForwardRelation φ p.1 p.2 q.1 q.2

/-- Uniform buffered symbols for an entire compact chart family. The complete
image of the closed input support, including shoulders, lies in an open output
plateau (`app:ch_regular:lem:finite-chain`). The geometric producer in the parent
factor construction must supply `hκ` and `himage` on the actual open input chart.
No extension or smoothness of the phase outside its conic domain is used. -/
theorem exists_bufferedLocalizers
    {P : Type*} [TopologicalSpace P] {T : Set P} (hT : IsCompact T)
    {K I O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hO : IsOpen O) (hKI : K ⊆ I)
    (κ : P → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (hκ : ContinuousOn (fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2)
      (T ×ˢ I))
    (himage : ∀ t ∈ T, ∀ p ∈ I, κ t p ∈ O) :
    ∃ mi mo : LocalizerSymbol n,
      IsBufferedLocalizer mi K I ∧
      IsBufferedLocalizer mo
        ((fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2) ''
          (T ×ˢ tsupport mi)) O ∧
      ∀ t ∈ T, ∀ p ∈ tsupport mi, κ t p ∈ interior {q | mo q = 1} := by
  obtain ⟨mi, hmi, hrange, hc, hs, hp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hI hKI
  have hsub : T ×ˢ tsupport mi ⊆ T ×ˢ I := prod_mono Subset.rfl hs
  have himcompact := (hT.prod hc).image_of_continuousOn (hκ.mono hsub)
  have himsub : (fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2) ''
      (T ×ˢ tsupport mi) ⊆ O := by
    rintro q ⟨⟨t, p⟩, ⟨ht, hpi⟩, rfl⟩
    exact himage t ht p (hs hpi)
  obtain ⟨mo, hmo, horange, hoc, hos, hop⟩ :=
    CompatibleResponse.exists_compact_family_cutoff himcompact hO himsub
  exact ⟨mi, mo, ⟨hmi, hrange, hc, hs, hp⟩,
    ⟨hmo, horange, hoc, hos, hop⟩,
    fun t ht p hpi => hop ⟨(t, p), ⟨ht, hpi⟩, rfl⟩⟩

/-- An open plateau excludes the closed support of the discarded identity
piece `1 - mo` (`app:ch_regular:lem:finite-chain`). -/
theorem notMem_complement_tsupport_of_mem_plateau
    {mo : LocalizerSymbol n} {q : Euclidean n × Euclidean n}
    (hq : q ∈ interior {q | mo q = 1}) :
    q ∉ tsupport (fun q => 1 - mo q) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [isOpen_interior.mem_nhds hq] with p hp
  exact sub_eq_zero.mpr (interior_subset hp).symm

/-- The same constructed masks have one geometric separation from the entire
closed complementary output support, uniformly over the compact chart family.
This gap is chosen before frequencies or integration orders
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_bufferedLocalizers_with_gap
    {P : Type*} [TopologicalSpace P] {T : Set P} (hT : IsCompact T)
    {K I O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hO : IsOpen O) (hKI : K ⊆ I)
    (κ : P → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (hκ : ContinuousOn (fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2)
      (T ×ˢ I))
    (himage : ∀ t ∈ T, ∀ p ∈ I, κ t p ∈ O) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧
      IsBufferedLocalizer mo
        ((fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2) ''
          (T ×ˢ tsupport mi)) O ∧
      (∀ t ∈ T, ∀ p ∈ tsupport mi, κ t p ∈ interior {q | mo q = 1}) ∧
      ∀ t ∈ T, ∀ p ∈ tsupport mi, ∀ q ∈ tsupport (fun q => 1 - mo q),
        δ < dist (κ t p) q := by
  obtain ⟨mi, mo, hi, ho, hbuffer⟩ := exists_bufferedLocalizers hT hK hI hO hKI κ hκ himage
  have hc := (hT.prod hi.compactSupport).image_of_continuousOn
    (hκ.mono (prod_mono Subset.rfl hi.support_subset))
  have hd : Disjoint
      ((fun p : P × (Euclidean n × Euclidean n) => κ p.1 p.2) ''
        (T ×ˢ tsupport mi)) (tsupport (fun q => 1 - mo q)) := by
    apply disjoint_left.mpr
    intro q hq
    exact notMem_complement_tsupport_of_mem_plateau (ho.plateau hq)
  obtain ⟨δ,hδ,hgap⟩ := CompatibleResponse.exists_uniform_source_gap hc
    (isClosed_tsupport _) hd
  exact ⟨mi, mo, δ, hδ, hi, ho, hbuffer,
    fun t ht p hp q hq => hgap (κ t p) ⟨(t,p), ⟨ht,hp⟩, rfl⟩ q hq⟩

/-- A common compact image envelope gives buffered masks and one geometric
separation for an arbitrary family of charts. No compactness of the phase
parameter space is required. The envelope and its containment in the output
chart are geometric inputs from the parent's compact physical support and
uniform covector bounds (`app:ch_regular:lem:finite-chain`). -/
theorem exists_bufferedLocalizers_of_image_envelope
    {P : Type*} {K I J O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hKI : K ⊆ I)
    (hJ : IsCompact J) (hO : IsOpen O) (hJO : J ⊆ O)
    (κ : P → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (himage : ∀ t p, p ∈ I → κ t p ∈ J) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧ IsBufferedLocalizer mo J O ∧
      (∀ t p, p ∈ tsupport mi → κ t p ∈ interior {q | mo q = 1}) ∧
      ∀ t p, p ∈ tsupport mi → ∀ q ∈ tsupport (fun q => 1 - mo q),
        δ < dist (κ t p) q := by
  obtain ⟨mi, hi, hir, hic, his, hip⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hK hI hKI
  obtain ⟨mo, ho, hor, hoc, hos, hop⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hJ hO hJO
  have hd : Disjoint J (tsupport (fun q => 1 - mo q)) := by
    apply disjoint_left.mpr
    exact fun q hq => notMem_complement_tsupport_of_mem_plateau (hop hq)
  obtain ⟨δ, hδ, hgap⟩ := CompatibleResponse.exists_uniform_source_gap hJ
    (isClosed_tsupport _) hd
  exact ⟨mi, mo, δ, hδ, ⟨hi,hir,hic,his,hip⟩, ⟨ho,hor,hoc,hos,hop⟩,
    fun t p hp => hop (himage t p (his hp)),
    fun t p hp q hq => hgap (κ t p) (himage t p (his hp)) q hq⟩

/-- The chart identity converts the constructed buffer to exclusion of the
full canonical relation on complementary closed supports. The identity is
supplied by the parent's inverse chart construction, for the chosen orientation
and actual output region (`app:ch_regular:eq:joint-stationary`). -/
theorem not_orientedRelation_of_buffer
    (backward : Bool) (φ : Euclidean n → Euclidean n → ℝ)
    {mi mo : LocalizerSymbol n} {R : Set (Euclidean n × Euclidean n)}
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (hbuffer : ∀ p ∈ tsupport mi, κ p ∈ interior {q | mo q = 1})
    (hchart : ∀ p ∈ tsupport mi, ∀ q ∈ R,
      orientedRelation backward φ p q → κ p = q)
    {p q : Euclidean n × Euclidean n}
    (hp : p ∈ tsupport mi) (hqR : q ∈ R)
    (hq : q ∈ tsupport (fun q => 1 - mo q)) :
    ¬ orientedRelation backward φ p q := by
  intro hrel
  have hplateau := hbuffer p hp
  rw [hchart p hp q hqR hrel] at hplateau
  exact notMem_complement_tsupport_of_mem_plateau hplateau hq

/-- Diagonal factors use the identity canonical chart in either orientation
(`app:ch_regular:lem:finite-chain`). -/
theorem orientedRelation_diagonal_iff (backward : Bool)
    (p q : Euclidean n × Euclidean n) :
    orientedRelation backward (fun u ξ => inner ℝ u ξ) p q ↔ p = q := by
  cases backward <;>
    simp only [orientedRelation, Bool.false_eq_true, ite_false, ite_true,
      diagonal_forwardRelation_iff, Prod.ext_iff]; tauto

end JanetCartan.FiniteChain.Graph
