module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.FrozenPhaseReference.NeighborhoodConstruction.FlowIdentities

/-!
# Neighborhood buffers for the retained frozen chart

Choose the covector neighborhood and physical ball needed by
`LocalFrozenReference` in `app:ch_seed:prop:seed-actual-menu`, Step 1, from
the open source and target of the retained `app:lem:common-hamilton-phase`
chart. The determinant differential is continuous by the shared polynomial
determinant API. The section embedding preserves the physical radius.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.FrozenPhaseReference
open HamiltonPhase

/-- Covector and physical buffers for the retained chart in
`app:lem:common-hamilton-phase` and `app:ch_seed:prop:seed-actual-menu`, Step 1.
This supplies the neighborhood fields of `LocalFrozenReference` for any
retained family; construction of that family and scalar-root uniqueness are
separate obligations of the local reference construction. -/
theorem exists_frozenReferenceNeighborhoods {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ≠ 0) (a : AdaptedSection ξ)
    {D : Set (Euclidean n × Euclidean n)} {R : ℝ} (hR : 0 < R)
    (F : FrozenHamiltonFamily a.embedding a.normal a.baseData ⟪a.normal, ξ⟫_ℝ D R) :
    ∃ (V : Set (Euclidean n)) (c ρ : ℝ),
      IsOpen V ∧ ξ ∈ V ∧ V ⊆ closedBall ξ R ∧
      (∀ p ∈ V, p ≠ 0) ∧ 0 < c ∧
      (∀ p ∈ V, c ≤ fderiv ℝ cubeDeterminant p a.normal) ∧ 0 < ρ ∧
      (∀ x ∈ ball (0 : Euclidean n) ρ, ∀ p ∈ V,
        (x, (0, a.embedding.toContinuousLinearMap.adjoint p)) ∈ F.chart.target) ∧
      (∀ u, a.embedding u ∈ ball (0 : Euclidean n) ρ → ∀ p ∈ V,
        (0, (u, (0, a.embedding.toContinuousLinearMap.adjoint p))) ∈ F.chart.source) := by
  have hbase : (0, (0, a.embedding.toContinuousLinearMap.adjoint ξ)) ∈
      F.chart.target := by
    rw [F.reference_control.target_eq]
    simpa [AdaptedSection.baseData] using F.base_mem
  have hbaseSource : ((0 : ℝ), a.baseData) ∈ F.chart.source := by
    have hb : ((0 : ℝ), a.baseData) ∈
        ball ((0 : ℝ), a.baseData) (3 * F.sourceRadius) :=
      mem_ball_self (mul_pos (by norm_num) F.sourceRadius_pos)
    have hs := (F.reference_control.source_admissible (subset_closure hb)).2
    rw [F.reference_control.source_eq]
    refine ⟨hb, ?_⟩
    simpa [HamiltonFlow.augmentedProjection, F.flow.initial_position a.baseData hs,
      F.reference_control.section_eq] using F.base_mem
  have htOpen : IsOpen {q : Euclidean n × Euclidean n |
      (q.1, (0, a.embedding.toContinuousLinearMap.adjoint q.2)) ∈ F.chart.target} :=
    F.chart.isOpen_target.preimage (continuous_fst.prodMk
      (continuous_const.prodMk (a.embedding.toContinuousLinearMap.adjoint.continuous.comp
        continuous_snd)))
  obtain ⟨rt, hrt, ht⟩ := Metric.isOpen_iff.mp htOpen (0, ξ) hbase
  have hsOpen : IsOpen {q : Euclidean (n - 1) × Euclidean n |
      (0, (q.1, (0, a.embedding.toContinuousLinearMap.adjoint q.2))) ∈ F.chart.source} :=
    F.chart.isOpen_source.preimage (continuous_const.prodMk (continuous_fst.prodMk
      (continuous_const.prodMk (a.embedding.toContinuousLinearMap.adjoint.continuous.comp
        continuous_snd))))
  obtain ⟨rs, hrs, hs⟩ := Metric.isOpen_iff.mp hsOpen (0, ξ) hbaseSource
  have hd : Continuous (fun p : Euclidean n ↦ fderiv ℝ cubeDeterminant p a.normal) := by
    have heq : determinant (cubeStress n) = cubeDeterminant :=
      funext determinant_cubeStress
    have hh : Continuous (fun p : Euclidean n ↦
        fderiv ℝ (determinant (cubeStress n)) p) :=
      (contDiff_fderiv_determinant (n := n)).continuous.comp
        (continuous_const.prodMk continuous_id)
    rw [heq] at hh
    exact hh.clm_apply continuous_const
  let c := fderiv ℝ cubeDeterminant ξ a.normal / 2
  have hc : 0 < c := half_pos a.determinant_positive
  have hcξ : c < fderiv ℝ cubeDeterminant ξ a.normal := half_lt_self a.determinant_positive
  let V : Set (Euclidean n) := ball ξ R ∩ ({p | p ≠ 0} ∩
    ({p | c < fderiv ℝ cubeDeterminant p a.normal} ∩ (ball ξ rt ∩ ball ξ rs)))
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_ne.inter
      ((isOpen_lt continuous_const hd).inter (isOpen_ball.inter isOpen_ball)))
  refine ⟨V, c, min rt rs, hV, ?_, ?_, ?_, hc, ?_, lt_min hrt hrs, ?_, ?_⟩
  · exact ⟨mem_ball_self hR, hξ, hcξ, mem_ball_self hrt, mem_ball_self hrs⟩
  · intro p hp
    exact ball_subset_closedBall hp.1
  · intro p hp
    exact hp.2.1
  · intro p hp
    exact hp.2.2.1.le
  · intro x hx p hp
    apply ht (a := (x, p))
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hx).trans_le (min_le_left _ _), hp.2.2.2.1⟩
  · intro u hu p hp
    apply hs (a := (u, p))
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, hp.2.2.2.2⟩
    have hu' : ‖u‖ < min rt rs := by
      simpa only [mem_ball, dist_zero_right, LinearIsometry.norm_map] using hu
    simpa only [dist_zero_right] using hu'.trans_le (min_le_right rt rs)

end JanetCartan.ActualCarriers.FrozenPhaseReference
