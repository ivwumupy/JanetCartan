module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.PatchFamily
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.ReferenceBuffer

/-!
# Constructing the finite quantitative full-phase menu

Choose the Hamilton families and their common targets before the final patch
shrinking. The existing decorated cover then preserves doubled closed patch
characteristicity, annular bounds, centered incidence sections and the full
image-channel detector. Every extra analytic premise is instantiated here
(`app:ch_seed:prop:seed-actual-menu`, Step 1).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

set_option maxHeartbeats 1600000 in
/-- Construct the finite decorated menu together with its actual quantitative
full-phase families in any prescribed physical ball inside the smooth frame
domain. No phase, flow, root or comparison estimate is assumed. The same
families subsequently supply arbitrary comparison tolerances, finite-order
continuity and sharp bounds (`app:ch_seed:prop:seed-actual-menu`, Step 1;
`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_quantitative_frozenReference_coverData {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : ball (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        ∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b := by
  let Decoration (P : Patch n) := {T : PatchQuantitativeFamily P U hU //
    ∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ ball (0 : Euclidean n) b}
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
    obtain ⟨N, hphysical, _hinj, γ, hγ, hgap⟩ :=
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
    exact ⟨P, c, C, hP, hcenter, hinc, ⟨⟨T, hphysical⟩⟩⟩
  obtain ⟨D, c, C, hD, hdec⟩ :=
    exists_decorated_coverData_of_local_patches hn Decoration hlocal
  let d (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) := Classical.choice (hdec i.1 i.2)
  exact ⟨D, c, C, hD, fun i ↦ (d i).val, fun i ↦ (d i).property⟩

/-- A finite minimum supplies one positive primitive frame threshold for all
patches at any requested positive full comparison tolerance. The returned
objects are actual `CarrierFullPhaseInput`s. Their charts are restrictions of
the already fixed families, so their phase bounds and continuity are those of
`PatchQuantitativeFamily.current_phase_bound` and `current_phase_continuity`
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem exists_common_fullPhaseInput_threshold {n : ℕ} {U : Set (Euclidean n)}
    {hU : IsOpen U} (D : CoverData n)
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (Q : Euclidean n → Fin n → MetricTensor n)
      (hQ : ContDiffOn ℝ ∞ Q U),
      (∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < δ) →
      ∀ i, ∃ hlow : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < (T i).family.threshold,
        ∃ I : CarrierFullPhaseInput (T i).reference (normalizedHomogeneousSymbol hU Q hQ) ε,
          I.flow = (T i).family.flow ⟨Q, hQ, hlow⟩ ∧
            HEq I.chart ((T i).currentChart ⟨Q, hQ, hlow⟩) := by
  choose d hd hc using fun i ↦ (T i).exists_fullPhaseInput_threshold hε
  obtain ⟨_r, δ, _K, _hr, _hr1, hδ, _hK, hcommon⟩ := exists_common_phase_buffers
    (fun i ↦ (T i).physicalRadius) (fun i ↦ min (T i).family.threshold (d i))
    (fun _ ↦ (1 : ℝ)) (fun i ↦ (T i).physicalRadius_pos)
    (fun i ↦ lt_min (T i).family.threshold_pos (hd i))
  refine ⟨δ, hδ, fun Q hQ hclose i ↦ ?_⟩
  have hlow := (hclose i).trans_le ((hcommon i).2.1.trans (min_le_left _ _))
  exact ⟨hlow, hc i ⟨Q, hQ, hlow⟩
    ((hclose i).trans_le ((hcommon i).2.1.trans (min_le_right _ _)))⟩

end JanetCartan.ActualCarriers.CurrentFullPhase
