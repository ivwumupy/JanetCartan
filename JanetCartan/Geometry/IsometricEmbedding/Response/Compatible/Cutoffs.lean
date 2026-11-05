module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Buffers
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A conjugate cutoff pair for an entire compact carrier family

The smooth partition in `app:ch_response:eq:response-whole-source-partition`,
including closed-support gaps for the opposite piece and the inactive difference.
The variable here is the normalized covector. Construction of the common energy
chart containing these directions is a separate prerequisite.
-/

@[expose] public noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace JanetCartan.CompatibleResponse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The negative angular piece in
`app:ch_response:eq:response-whole-source-partition`. -/
def antipodalCutoff (a : E → ℝ) : E → ℝ := fun ξ ↦ a (-ξ)

/-- The whole angular partition in
`app:ch_response:eq:response-whole-source-partition`. -/
def symmetricCutoff (a : E → ℝ) : E → ℝ := fun ξ ↦ a ξ + antipodalCutoff a ξ

/-- The negative piece is smooth whenever the positive one is smooth
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem contDiff_antipodalCutoff {a : E → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (antipodalCutoff a) :=
  ha.comp contDiff_id.neg

omit [NormedSpace ℝ E] in
/-- The whole partition is even
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem symmetricCutoff_neg (a : E → ℝ) (ξ : E) :
    symmetricCutoff a (-ξ) = symmetricCutoff a ξ := by
  simp [symmetricCutoff, antipodalCutoff, add_comm]

omit [NormedSpace ℝ E] in
/-- Closed support, including all shoulders, transforms by the exact antipode
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem tsupport_antipodalCutoff (a : E → ℝ) :
    tsupport (antipodalCutoff a) = Neg.neg ⁻¹' tsupport a :=
  tsupport_comp_eq_preimage a (Homeomorph.neg E)

omit [NormedSpace ℝ E] in
/-- A plateau neighborhood excludes the entire closed support of `a - 1`,
not only its nonzero set (`app:ch_response:thm:response-compatible-choice`). -/
theorem disjoint_inactive_tsupport {K : Set E} {a : E → ℝ}
    (hp : K ⊆ interior {ξ | a ξ = 1}) :
    Disjoint K (tsupport (fun ξ ↦ a ξ - 1)) := by
  apply disjoint_left.mpr
  intro ξ hξ
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_)
  filter_upwards [isOpen_interior.mem_nhds (hp hξ)] with v hv
  have hv' : v ∈ {w | a w = 1} := interior_subset hv
  exact sub_eq_zero.mpr hv'

/-- Construct a smooth cutoff for a whole compact set with both a plateau
neighborhood and closed support inside its open chart
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_compact_family_cutoff [FiniteDimensional ℝ E]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ (∀ ξ, a ξ ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport a ∧ tsupport a ⊆ O ∧ K ⊆ interior {ξ | a ξ = 1} := by
  obtain ⟨V, hV, hKV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨W, hW, hKW, hWV, _⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨a, ha, harange, hasupp, haone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  have hts : tsupport a = closure V := by rw [tsupport, hasupp]
  refine ⟨a, ha, fun ξ ↦ harange (mem_range_self ξ), ?_, ?_, ?_⟩
  · change IsCompact (tsupport a)
    rwa [hts]
  · rwa [hts]
  · apply hKW.trans
    exact interior_maximal (fun ξ hξ ↦ (haone ξ).mp (subset_closure hξ)) hW

/-- A single smooth response plateau lies in all finitely many pointed patch
cores (`app:ch_response:thm:response-compatible-choice`). Its radius and function
are chosen before any frequency, sampling count, or accuracy parameter. -/
theorem exists_common_response_plateau [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    {p : E} (hp : ∀ i, p ∈ U i) :
    ∃ (r : ℝ) (χ : E → ℝ), 0 < r ∧ ContDiff ℝ ∞ χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      (∀ i, tsupport χ ⊆ U i) ∧ Metric.closedBall p r ⊆ interior {x | χ x = 1} := by
  obtain ⟨r, hr, hball⟩ := exists_common_response_ball U hU hp
  have hsub : Metric.closedBall p r ⊆ ⋂ i, U i := by
    intro x hx
    exact mem_iInter.mpr (fun i ↦ hball i
      (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r) hx))
  obtain ⟨χ, hχ, hrange, hcompact, hsupp, hplateau⟩ := exists_compact_family_cutoff
    (isCompact_closedBall p r) (isOpen_iInter_of_finite hU) hsub
  exact ⟨r, χ, hr, hχ, hrange, hcompact,
    fun i x hx ↦ mem_iInter.mp (hsupp hx) i, hplateau⟩

omit [NormedSpace ℝ E] in
/-- A compact positive family disjoint from its antipode has an antipodally
disjoint open neighborhood inside any prescribed open energy chart
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_antipodal_subchart {K O : Set E} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hdis : Disjoint K (Neg.neg ⁻¹' K)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ Disjoint V (Neg.neg ⁻¹' V) := by
  obtain ⟨U, W, hU, hW, hKU, hKW, hUW⟩ :=
    normal_separation hK.isClosed (hK.isClosed.preimage continuous_neg) hdis
  refine ⟨O ∩ U ∩ Neg.neg ⁻¹' W, (hO.inter hU).inter (hW.preimage continuous_neg),
    ?_, fun _ hx ↦ hx.1.1, ?_⟩
  · intro x hx
    exact ⟨⟨hKO hx, hKU hx⟩, hKW (by simpa using hx)⟩
  · apply disjoint_left.mpr
    intro x hx hnx
    exact disjoint_left.mp hUW hx.1.2 (by simpa using hnx.2)

/-- Choose the positive cutoff once for the whole protected compact family.
Its antipodal piece and the complete inactive difference have one strictly
positive normalized source gap, including their shoulders
(`app:ch_response:thm:response-compatible-choice`).

The open energy chart and its disjointness from its antipode are explicit
geometric inputs, not asserted consequences of a phase construction here. -/
theorem exists_conjugate_cutoff_source_gap [FiniteDimensional ℝ E]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hdis : Disjoint O (Neg.neg ⁻¹' O)) :
    ∃ (a : E → ℝ) (δ : ℝ), 0 < δ ∧ ContDiff ℝ ∞ a ∧
      (∀ ξ, a ξ ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport a ∧ tsupport a ⊆ O ∧
      K ⊆ interior {ξ | a ξ = 1} ∧
      Disjoint (tsupport a) (tsupport (antipodalCutoff a)) ∧
      ∀ x ∈ K, ∀ y ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun ξ ↦ a ξ - 1),
        δ < dist x y := by
  obtain ⟨a, ha, harange, hacompact, hasupp, haplateau⟩ :=
    exists_compact_family_cutoff hK hO hKO
  have hneg : tsupport (antipodalCutoff a) ⊆ Neg.neg ⁻¹' O := by
    rw [tsupport_antipodalCutoff]
    exact preimage_mono hasupp
  have hpair := hdis.mono hasupp hneg
  have hprotected := hdis.mono hKO hneg
  have hinactive := disjoint_inactive_tsupport haplateau
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_source_gap hK
    ((isClosed_tsupport _).union (isClosed_tsupport _))
    (disjoint_union_right.mpr ⟨hprotected, hinactive⟩)
  exact ⟨a, δ, hδ, ha, harange, hacompact, hasupp, haplateau, hpair, hgap⟩

omit [NormedSpace ℝ E] in
/-- The same normalized gap applies to the negative primary sign, with the
positive piece now inactive and the negative plateau difference retained
(`app:ch_response:thm:response-compatible-choice`). -/
theorem antipodal_source_gap {K : Set E} {a : E → ℝ} {δ : ℝ}
    (hgap : ∀ x ∈ K,
      ∀ y ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun ξ ↦ a ξ - 1),
        δ < dist x y) :
    ∀ x ∈ Neg.neg ⁻¹' K,
      ∀ y ∈ tsupport a ∪ tsupport (fun ξ ↦ antipodalCutoff a ξ - 1),
        δ < dist x y := by
  intro x hx y hy
  have hny : -y ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun ξ ↦ a ξ - 1) := by
    rcases hy with hy | hy
    · left
      simpa only [tsupport_antipodalCutoff, mem_preimage, neg_neg] using hy
    · right
      exact tsupport_comp_subset_preimage (fun ξ ↦ a ξ - 1) continuous_neg hy
  simpa only [dist_neg_neg] using hgap (-x) hx (-y) hny

/-- The two smooth conjugate angular cutoffs and both source gaps can be chosen
from a compact antipodally separated family in an open chart, before sampling
or frequencies (`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_two_sign_cutoff_gaps [FiniteDimensional ℝ E]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hdis : Disjoint K (Neg.neg ⁻¹' K)) :
    ∃ (a : E → ℝ) (δ : ℝ), 0 < δ ∧ ContDiff ℝ ∞ a ∧
      ContDiff ℝ ∞ (antipodalCutoff a) ∧
      (∀ ξ, a ξ ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport a ∧ tsupport a ⊆ O ∧
      K ⊆ interior {ξ | a ξ = 1} ∧
      Disjoint (tsupport a) (tsupport (antipodalCutoff a)) ∧
      (∀ x ∈ K, ∀ y ∈ tsupport (antipodalCutoff a) ∪ tsupport (fun ξ ↦ a ξ - 1),
        δ < dist x y) ∧
      (∀ x ∈ Neg.neg ⁻¹' K,
        ∀ y ∈ tsupport a ∪ tsupport (fun ξ ↦ antipodalCutoff a ξ - 1),
          δ < dist x y) := by
  obtain ⟨V, hV, hKV, hVO, hVV⟩ := exists_antipodal_subchart hK hO hKO hdis
  obtain ⟨a, δ, hδ, ha, harange, hacompact, hasupp, haplateau, hpair, hgap⟩ :=
    exists_conjugate_cutoff_source_gap hK hV hKV hVV
  exact ⟨a, δ, hδ, ha, contDiff_antipodalCutoff ha, harange, hacompact,
    hasupp.trans hVO, haplateau, hpair, hgap, antipodal_source_gap hgap⟩

end JanetCartan.CompatibleResponse
