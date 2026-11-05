module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.AngularNeighborhood

/-!
# Fixed regular sectors for the complete source and comparison images

The sectors in `app:ch_regular:thm:no-return` enclose both the annular source
and its normalization, together with every comparison graph direction.
The enclosing set supplied by the comparison producer is fixed before the
current frame. Taking its symmetric hull includes both orientations without
requiring symmetry of the selected finite comparison charts.
-/

@[expose] public noncomputable section
open Set Metric

namespace JanetCartan.ProtectedFlow

/-- The forbidden cone is symmetric (`app:ch_seed:prop:seed-strata`). -/
theorem neg_not_mem_cubeBadSubspaceUnion {n : ℕ} {v : Euclidean n}
    (hv : v ∉ cubeBadSubspaceUnion n) : -v ∉ cubeBadSubspaceUnion n := by
  intro h
  obtain ⟨L, hL, hvL⟩ := mem_iUnion₂.mp h
  exact hv (mem_iUnion₂.mpr ⟨L, hL, by simpa using L.neg_mem hvL⟩)

/-- Two fixed compact symmetric regular sectors enclose the entire source,
its normalized elliptic points, and the uniform comparison-gradient enclosure.
The positive buffer lies in the *interior* of the inner sector and avoids the
actual forbidden cone (`app:ch_regular:thm:no-return`). This is consumed by
`exists_extended_frame_protection`. -/
theorem exists_regular_source_sectors {n : ℕ} (hn : 5 ≤ n)
    {Ω A : Set (Euclidean n)} (hΩ : IsCompact Ω) (hA : IsCompact A)
    (hΩbad : Disjoint Ω (cubeBadSubspaceUnion n))
    (hAbad : A ⊆ (cubeBadSubspaceUnion n)ᶜ) :
    ∃ Γin Γout : Set (Euclidean n), ∃ ε > (0 : ℝ),
      IsCompact Γin ∧ IsCompact Γout ∧ Γin ⊆ interior Γout ∧
      (∀ v ∈ Γin, -v ∈ Γin) ∧ (∀ v ∈ Γout, -v ∈ Γout) ∧
      Γout ⊆ (cubeBadSubspaceUnion n)ᶜ ∧ Ω ⊆ interior Γin ∧
      (∀ v ∈ Ω, closedBall (normalizedCovector v) ε ⊆
        interior Γin \ cubeBadSubspaceUnion n) ∧
      (∀ v ∈ A, closedBall v ε ⊆ interior Γin \ cubeBadSubspaceUnion n) := by
  have hΩne (v : Euclidean n) (hv : v ∈ Ω) : v ≠ 0 := by
    rintro rfl
    exact disjoint_left.mp hΩbad hv (zero_mem_cubeBadSubspaceUnion hn)
  have hncont : ContinuousOn (normalizedCovector : Euclidean n → Euclidean n) Ω :=
    (continuousOn_id.norm.inv₀ (fun v hv ↦ norm_ne_zero_iff.mpr (hΩne v hv))).smul
      continuousOn_id
  let B := Ω ∪ normalizedCovector '' Ω ∪ A
  let K := B ∪ (fun v ↦ -v) '' B
  have hB : IsCompact B := (hΩ.union (hΩ.image_of_continuousOn hncont)).union hA
  have hK : IsCompact K := hB.union (hB.image continuous_neg)
  have hBbad : B ⊆ (cubeBadSubspaceUnion n)ᶜ := by
    rintro v ((hv | ⟨w, hw, rfl⟩) | hv)
    · exact disjoint_left.mp hΩbad hv
    · exact normalizedCovector_not_mem_cubeBadSubspaceUnion (hΩne w hw)
        (disjoint_left.mp hΩbad hw)
    · exact hAbad hv
  have hKbad : K ⊆ (cubeBadSubspaceUnion n)ᶜ := by
    rintro v (hv | ⟨w, hw, rfl⟩)
    · exact hBbad hv
    · exact neg_not_mem_cubeBadSubspaceUnion (hBbad hw)
  have hKsym (v : Euclidean n) (hv : v ∈ K) : -v ∈ K := by
    rcases hv with hv | ⟨w, hw, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
    · rw [neg_neg]
      exact Or.inl hw
  obtain ⟨d, hd, hdK⟩ := hK.exists_cthickening_subset_open
    (isClosed_cubeBadSubspaceUnion n).isOpen_compl hKbad
  let ε := d / 8
  have hε : 0 < ε := div_pos hd (by norm_num)
  let Γin := cthickening (2 * ε) K
  let Γout := cthickening (4 * ε) K
  have hinside : Γout ⊆ (cubeBadSubspaceUnion n)ᶜ :=
    (cthickening_mono (by dsimp [ε]; linarith) K).trans hdK
  have hnest : Γin ⊆ interior Γout :=
    (cthickening_subset_thickening' (by positivity : 0 < 4 * ε)
      (by linarith) K).trans (thickening_subset_interior_cthickening _ _)
  have hsym {a : ℝ} (ha : 0 ≤ a) {v : Euclidean n}
      (hv : v ∈ cthickening a K) : -v ∈ cthickening a K := by
    rw [hK.cthickening_eq_biUnion_closedBall ha] at hv ⊢
    obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.mp hv
    exact mem_iUnion₂.mpr ⟨-w, hKsym w hw, by simpa using hvw⟩
  have hbuffer (v : Euclidean n) (hv : v ∈ K) :
      closedBall v ε ⊆ interior Γin \ cubeBadSubspaceUnion n := by
    intro w hw
    have hh : w ∈ interior Γin :=
      ((closedBall_subset_cthickening hv ε).trans
        ((cthickening_subset_thickening' (by positivity : 0 < 2 * ε)
          (by linarith) K).trans (thickening_subset_interior_cthickening _ _))) hw
    exact ⟨hh, hinside (interior_subset (hnest (interior_subset hh)))⟩
  refine ⟨Γin, Γout, ε, hε, hK.cthickening, hK.cthickening, hnest,
    fun _ hv ↦ hsym (by positivity) hv, fun _ hv ↦ hsym (by positivity) hv,
    hinside, ?_, ?_, ?_⟩
  · intro v hv
    exact (hbuffer v (Or.inl (Or.inl (Or.inl hv))) (mem_closedBall_self hε.le)).1
  · intro v hv
    exact hbuffer _ (Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  · intro v hv
    exact hbuffer _ (Or.inl (Or.inr hv))

end JanetCartan.ProtectedFlow
