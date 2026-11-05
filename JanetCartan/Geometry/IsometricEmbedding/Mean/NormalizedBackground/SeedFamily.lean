module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FiniteFamily

/-!
# A retained finite Hamilton family for the actual flat seed

The normalized-background construction needs both a compact coefficient domain
and the frozen transverse gap used in source-chart matching. The ordinary finite
Hamilton constructor discards the latter witness. Here the same decorated-cover
construction retains it, before any source scale is chosen
(`app:ch_background:prop:bg-normalized`, `app:ch_seed:prop:seed-actual-menu`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers HamiltonPhase FrozenMenu FrozenPhaseReference CurrentFullPhase

/-- Retain the actual whole-state-ball transverse gap while constructing the
finite quantitative Hamilton family. This is the frozen input to the SAME
seed transports and source-chart matching, not an assumed gap of a current
phase (`app:ch_background:eq:bg-Nsigma`). -/
theorem exists_transverse_retained_seed_family {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : ball (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        ∃ γ > 0, ∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
            (T i).data.localReference.stateRadius,
          γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ| := by
  let Decoration (P : Patch n) := {T : PatchQuantitativeFamily P U hU //
    (∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
    ∃ γ > 0, ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      γ ≤ |⟪(frozenSymbol n).hp q, T.data.adapted.normal⟫_ℝ|}
  have hlocal : ∀ (k s ξ : Euclidean n), CarrierSeed k s ξ →
      ∃ (P : Patch n) (c C : ℝ), P.IsValid c C ∧ P.toFun 0 = ξ ∧
        (∀ z ∈ parameterCube P.radius,
          c ≤ |fderiv ℝ (fun w ↦ incidence k (P.toFun w)) z (EuclideanSpace.single 0 1)|) ∧
        Nonempty (Decoration P) := by
    intro k s ξ hseed
    obtain ⟨a⟩ := exists_adaptedSection_of_carrierSeed hn hseed
    have hξ : ξ ≠ 0 := by
      intro hzero
      exact hseed.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hzero])
    obtain ⟨N, hphysical, _, γ, hγ, hgap⟩ :=
      exists_transverse_localFrozenReference_in_physical_ball hξ hseed.characteristic a hb
    obtain ⟨L⟩ := exists_localQuantitativeFamily hξ hseed.characteristic a N
      (fun q hq ↦ abs_pos.mp (hγ.trans_le (hgap q hq))) hU
      (fun q hq ↦ hBU (hphysical q hq))
    let V := N.covectorSet ∩ (fun p ↦ (0, a.embedding.toContinuousLinearMap.adjoint p)) ⁻¹'
      ball a.baseData.2 (min L.radius (3 * L.sourceRadius))
    have hV : IsOpen V := N.covectorSet_open.inter
      (isOpen_ball.preimage (continuous_const.prodMk
        a.embedding.toContinuousLinearMap.adjoint.continuous))
    have hξV : ξ ∈ V := by
      refine ⟨N.covectorSet_base, ?_⟩
      change a.baseData.2 ∈ ball a.baseData.2 _
      exact mem_ball_self (lt_min L.radius_pos (mul_pos (by norm_num) L.sourceRadius_pos))
    obtain ⟨P, c, C, hP, hcenter, hinc, hbuffer⟩ := exists_valid_patch_in_open hn hseed hV hξV
    let d : FrozenPatchData P := ⟨ξ, a, N, hcenter,
      fun z hz ↦ (hbuffer z hz).1.1, fun z hz ↦ (hbuffer z hz).2.1,
      c, C, hP.2.1, fun z hz ↦ (hbuffer z hz).2.2.2⟩
    let T : PatchQuantitativeFamily P U hU := ⟨d, L, fun z hz ↦ (hbuffer z hz).1.2⟩
    exact ⟨P, c, C, hP, hcenter, hinc, ⟨⟨T, hphysical, γ, hγ, hgap⟩⟩⟩
  obtain ⟨D, c, C, hD, hdec⟩ :=
    exists_decorated_coverData_of_local_patches hn Decoration hlocal
  let d (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) := Classical.choice (hdec i.1 i.2)
  choose γ hγ hgap using fun i ↦ (d i).property.2
  obtain ⟨γ₀, hγ₀, hmin⟩ := (finite_range γ).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨i, rfl⟩; exact hγ i)
  exact ⟨D, c, C, hD, fun i ↦ (d i).val, fun i ↦ (d i).property.1,
    γ₀, hγ₀, fun i q hq ↦ (hmin _ ⟨i, rfl⟩).trans (hgap i q hq)⟩

/-- Construct the genuine flat reference and finite retained Hamilton family
with every primitive domain input required by
`exists_flat_seed_normalized_mean`. The common frozen transverse gap is also
retained for `SourceMatching`, before choosing the seed or source scale
(`app:ch_background:prop:bg-normalized`). -/
theorem exists_flat_seed_family {n : ℕ} (hn : 5 ≤ n) :
    ∃ (G : FlatReference n) (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (G.domain.chart n) isOpen_ball,
        let K := closedBall (0 : Euclidean n) (G.domain.chartRadius / 2)
        IsCompact K ∧ K ⊆ G.domain.chart n ∧
        (∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K) ∧
        ∃ γ > 0, ∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
            (T i).data.localReference.stateRadius,
          γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ| := by
  obtain ⟨G, _⟩ := exists_analytic_flatReference hn
  have hr : 0 < G.domain.chartRadius :=
    G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius
  obtain ⟨D, c, C, hD, T, hphysical, hgap⟩ :=
    exists_transverse_retained_seed_family hn (U := G.domain.chart n) isOpen_ball
      (half_pos hr) (ball_subset_ball (half_le_self hr.le))
  refine ⟨G, D, c, C, hD, T, isCompact_closedBall _ _,
    closedBall_subset_ball (half_lt_self hr), ?_, hgap⟩
  intro i x hx
  apply ball_subset_closedBall
  apply hphysical i (x, (T i).data.center)
  apply (T i).data.localReference.stateBall_subset
  rw [(T i).data.adapted.baseState_eq]
  simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hx

end JanetCartan.NormalizedBackground
