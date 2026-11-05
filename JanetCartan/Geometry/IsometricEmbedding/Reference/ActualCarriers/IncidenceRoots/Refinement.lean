module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.FiniteData

/-!
# A fixed smaller finite cover for actual incidence continuation

Construct the buffered cylinders from the published frozen cover, before any
current phase or perturbation accuracy is chosen. This is the finite-cover
step of `app:ch_seed:prop:seed-actual-menu`, Step 3.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace JanetCartan.ActualCarriers

open FrozenMenu CharacteristicRoot

/-- The frozen incidence sections construct a finite refinement by buffered
balls and transverse scalar cylinders. All selected source patches are retained,
including the possibility of empty patch lists
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem exists_valid_incidenceRefinement {n : ℕ} {D : CoverData n} {c₀ C₀ : ℝ}
    (hD : D.IsValid c₀ C₀) : ∃ R : IncidenceRefinement D, R.IsValid := by
  classical
  have hlocal (b : Fin D.chartCount) (k : Euclidean n) (hk : k ∈ D.domain b) :
      ∃ (r : ℝ) (a c e : Fin (D.patchCount b) → ℝ),
        0 < r ∧ Metric.closedBall k (2 * r) ⊆ D.domain b ∧
        ∀ i, 0 < a i ∧ 0 < c i ∧ 0 < e i ∧
          (∀ t ∈ Icc (-a i) (a i),
            incidenceParameter (D.roots b i k) t ∈ parameterInterior (D.patches b i).radius) ∧
          (∀ q ∈ Metric.closedBall k (2 * r), ∀ t ∈ Icc (-a i) (a i),
            2 * c i ≤ |scalarDerivative
              (frozenDeterminantIncidence (D.patches b i) (D.roots b i k)) (q, t)|) ∧
          (∀ q ∈ Metric.closedBall k (2 * r),
            (frozenDeterminantIncidence (D.patches b i) (D.roots b i k) (q, -a i) ≤ -e i ∧
              e i ≤ frozenDeterminantIncidence (D.patches b i) (D.roots b i k) (q, a i)) ∨
            (frozenDeterminantIncidence (D.patches b i) (D.roots b i k) (q, a i) ≤ -e i ∧
              e i ≤ frozenDeterminantIncidence (D.patches b i) (D.roots b i k) (q, -a i))) := by
    choose r a c e hr ha hc he hi hg hend using fun i ↦
      exists_frozen_incidence_cylinder_of_section (hD.2.2.2.2.1 b i).1
        (hD.2.2.2.2.1 b i).2 hD.1 hk
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((hD.2.2.1 b).mem_nhds hk)
    obtain ⟨s, hs, hsr⟩ := Pi.exists_forall_pos_add_lt hr
    let R := min s (ρ / 2)
    have hR : 0 < R := lt_min hs (half_pos hρ)
    have hRi (i) : R ≤ r i := (min_le_left _ _).trans (by simpa using (hsr i).le)
    refine ⟨R, a, c, e, hR, ?_, fun i ↦ ⟨ha i, hc i, he i, hi i, ?_, ?_⟩⟩
    · exact (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith [min_le_right s (ρ / 2)])).trans hρsub
    · intro q hq t ht
      exact hg i q (Metric.closedBall_subset_closedBall (by linarith [hRi i]) hq) t ht
    · intro q hq
      exact hend i q (Metric.closedBall_subset_closedBall (by linarith [hRi i]) hq)
  let S := Metric.sphere (0 : Euclidean n) 1
  have hsource : ∀ k : S, ∃ b, k.val ∈ D.domain b :=
    fun k ↦ mem_iUnion.mp (hD.2.2.2.1 k.property)
  choose b hb using hsource
  choose r a c e hr hsub hbounds using fun k : S ↦ hlocal (b k) k.val (hb k)
  have hcover : S ⊆ ⋃ k : S, Metric.ball k.val (r k) := by
    intro k hk
    exact mem_iUnion.mpr ⟨⟨k, hk⟩, Metric.mem_ball_self (hr ⟨k, hk⟩)⟩
  obtain ⟨t, ht⟩ := (isCompact_sphere (0 : Euclidean n) 1).elim_finite_subcover
    (fun k : S ↦ Metric.ball k.val (r k)) (fun _ ↦ Metric.isOpen_ball) hcover
  let f := t.equivFin.symm
  let R : IncidenceRefinement D :=
    { chartCount := t.card
      sourceChart := fun j ↦ b (f j).val
      center := fun j ↦ (f j).val.val
      radius := fun j ↦ r (f j).val
      halfWidth := fun j ↦ a (f j).val
      gap := fun j ↦ c (f j).val
      endpointMargin := fun j ↦ e (f j).val }
  refine ⟨R, fun j ↦ hr (f j).val, fun j ↦ hsub (f j).val, ?_,
    fun j ↦ hbounds (f j).val⟩
  intro k hk
  obtain ⟨j, hj, hkj⟩ := mem_iUnion₂.mp (ht hk)
  refine mem_iUnion.mpr ⟨f.symm ⟨j, hj⟩, ?_⟩
  simpa [R] using hkj

end JanetCartan.ActualCarriers
