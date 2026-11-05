module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.NormalizedHistory.ChartCenters.DecoratedCover
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.HamiltonDependence.RetainedGeometry

/-!
# Positive Hamilton geometry with retained chart centers on one menu

The decorated-cover selection for `app:ch_background:prop:bg-normalized`
retains both the original whole-state-ball frozen gap and the smaller current
Hamilton state ball and inverse gap from `app:lem:common-hamilton-phase`.
The same local families and actual selected unit-sphere chart centers are passed
to `exists_common_normalized_history_reference_retained_leading_with_chart_centers`.
This supplies directions in the same chart domains before frame tolerances or
source scales, as required by `app:ch_background:defn:bg-row`.
Its consumer `PositiveReference.exists_retained_carrier_immersion_tolerance`
uses precisely these witnesses for `app:ch_background:prop:bg-frame` and
`paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ReferenceInitialization.NormalizedHistory
open ActualCarriers HamiltonPhase FrozenMenu FrozenPhaseReference CurrentFullPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference

/-- Construct one decorated Hamilton menu retaining the frozen transverse gap,
physical containment, Hamilton position smoothness and the positive-reference comparison geometry. The latter
is exactly the input of `PositiveReference.exists_retained_carrier_immersion_tolerance`.
Each chart retains its actual center in the unit sphere and its own domain
(`app:ch_seed:prop:seed-frozen-menu`). All witnesses precede the source scale and
every admitted current frame
(`app:lem:common-hamilton-phase`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_positive_geometry_retained_seed_family_with_chart_centers_and_position_smoothness
    {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : ball (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ kCenter : Fin D.chartCount → Euclidean n,
        (∀ b, kCenter b ∈ sphere (0 : Euclidean n) 1) ∧
        (∀ b, kCenter b ∈ D.domain b) ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i Q, ContDiffOn ℝ ∞ ((T i).family.flow Q).position
          (((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters)) ∧
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        (∀ i, ∃ (Rinner : ℝ)
          (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
            (Euclidean n × (ℝ × Euclidean (n - 1)))),
          0 < Rinner ∧ Rinner < (T i).data.localReference.stateRadius ∧
          (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData)
              (3 * (T i).family.sourceRadius),
            ‖(A.symm : _ →L[ℝ] _).comp
                (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
              ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
          (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
            (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
              closedBall (0, (T i).data.center) Rinner) ∧
          (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
            ∀ z ∈ closedBall (0, (T i).data.center) Rinner,
              ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z,
                (T i).data.adapted.normal⟫_ℝ ≠ 0)) ∧
        ∃ γ > 0, ∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
            (T i).data.localReference.stateRadius,
          γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ| := by
  let Decoration (P : Patch n) := {T : PatchQuantitativeFamily P U hU //
    (∀ Q, ContDiffOn ℝ ∞ (T.family.flow Q).position
      ((T.family.flow Q).time ×ˢ (T.family.flow Q).parameters)) ∧
    (∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b) ∧
    (∃ γ > 0, ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      γ ≤ |⟪(frozenSymbol n).hp q, T.data.adapted.normal⟫_ℝ|) ∧
    ∃ (Rinner : ℝ)
      (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
        (Euclidean n × (ℝ × Euclidean (n - 1)))),
      0 < Rinner ∧ Rinner < T.data.localReference.stateRadius ∧
      (∀ Q, ∀ q ∈ ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius),
        ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ (T.family.flow Q).augmentedProjection q) -
          ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
      (∀ Q, ∀ q ∈ (T.family.flow Q).time ×ˢ (T.family.flow Q).parameters,
        ((T.family.flow Q).position q, (T.family.flow Q).momentum q) ∈
          closedBall (0, T.data.center) Rinner) ∧
      (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
        ∀ z ∈ closedBall (0, T.data.center) Rinner,
          ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)}
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
    obtain ⟨L, Rinner, A, hRinner, hRinnerN, hgeometry⟩ :=
      exists_localQuantitativeFamily_with_transverse_control hξ hseed.characteristic a N
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
    exact ⟨P, c, C, hP, hcenter, hinc, ⟨⟨T, fun Q ↦ (hgeometry Q).2.2.2.2,
      hphysical, ⟨γ, hγ, hgap⟩,
      Rinner, A, hRinner, hRinnerN, fun Q ↦ (hgeometry Q).2.1,
      fun Q ↦ (hgeometry Q).2.2.1, fun Q ↦ (hgeometry Q).2.2.2.1⟩⟩⟩
  obtain ⟨D, c, C, hD, kCenter, hkCenter, hkDomain, hdec⟩ :=
    exists_decorated_coverData_with_chart_centers_of_local_patches hn Decoration hlocal
  let d (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) := Classical.choice (hdec i.1 i.2)
  choose γ hγ hgap using fun i ↦ (d i).property.2.2.1
  obtain ⟨γ₀, hγ₀, hmin⟩ := (finite_range γ).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨i, rfl⟩; exact hγ i)
  exact ⟨D, c, C, hD, kCenter, hkCenter, hkDomain, fun i ↦ (d i).val,
    fun i ↦ (d i).property.1, fun i ↦ (d i).property.2.1,
    fun i ↦ (d i).property.2.2.2,
    γ₀, hγ₀, fun i q hq ↦ (hmin _ ⟨i, rfl⟩).trans (hgap i q hq)⟩

/-- The original frozen-menu API is the projection of the selection retaining
Hamilton position smoothness. All physical, transverse and positive-reference
witnesses belong to that same selected family
(`app:ch_seed:prop:seed-frozen-menu`, `app:lem:common-hamilton-phase`). -/
theorem exists_positive_geometry_retained_seed_family_with_chart_centers {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : ball (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ kCenter : Fin D.chartCount → Euclidean n,
        (∀ b, kCenter b ∈ sphere (0 : Euclidean n) 1) ∧
        (∀ b, kCenter b ∈ D.domain b) ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        (∀ i, ∃ (Rinner : ℝ)
          (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
            (Euclidean n × (ℝ × Euclidean (n - 1)))),
          0 < Rinner ∧ Rinner < (T i).data.localReference.stateRadius ∧
          (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData)
              (3 * (T i).family.sourceRadius),
            ‖(A.symm : _ →L[ℝ] _).comp
                (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
              ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
          (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
            (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
              closedBall (0, (T i).data.center) Rinner) ∧
          (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
            ∀ z ∈ closedBall (0, (T i).data.center) Rinner,
              ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z,
                (T i).data.adapted.normal⟫_ℝ ≠ 0)) ∧
        ∃ γ > 0, ∀ i, ∀ q ∈ closedBall (0, (T i).data.center)
            (T i).data.localReference.stateRadius,
          γ ≤ |⟪(frozenSymbol n).hp q, (T i).data.adapted.normal⟫_ℝ| := by
  obtain ⟨D, c, C, hD, kCenter, hkCenter, hkDomain, T, _hposition, hrest⟩ :=
    exists_positive_geometry_retained_seed_family_with_chart_centers_and_position_smoothness
      hn hU hb hBU
  exact ⟨D, c, C, hD, kCenter, hkCenter, hkDomain, T, hrest⟩

end JanetCartan.ReferenceInitialization.NormalizedHistory
