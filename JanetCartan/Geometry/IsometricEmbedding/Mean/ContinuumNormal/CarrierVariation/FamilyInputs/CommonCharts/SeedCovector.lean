module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.FrozenReference
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling

/-!
# Identifying the actual flat seed covector

For `paper-v2.tex`, `new:lem:scaling` and `app:ch_background:eq:bg-Psi`,
the seed frame at the physical origin is the cube frame. The eikonal equation
and the Cauchy section therefore give the same energy and tangential momentum
as the frozen covector. The named producer `exists_frozenRootBuffer` supplies
local root uniqueness; `LocalQuantitativeFamily.exists_momentum_comparison_threshold`
puts the actual covector in that root neighborhood. This derives the exact
zero-section identity required by `exists_source_common_conic_charts`.

Only a primitive frame threshold remains for the chosen seed. For an actual
`FlatReference`, `projectedStress_flatReference_zero` supplies the origin
identity, and `exists_projectedStress_dilation_bounds` supplies arbitrarily
small frame norms after source contraction. No inverse or differential-gap
hypothesis is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase ActualComparison
open HamiltonPhase FrozenPhaseReference ContinuumRow.CanonicalConic ContinuumRow.CanonicalCarrier
variable {n : ℕ} {P : Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : PatchQuantitativeFamily P U₀ hU₀)

private theorem seed_phase_target
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : Euclidean (n - 1)}
    (hη : η ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    (x, (0, η)) ∈ T.target := by
  have hpr : T.physicalRadius < T.family.radius := by
    have hh := min_le_left T.family.radius (3 * T.family.sourceRadius)
    have hp := T.physicalRadius_pos
    dsimp [PatchQuantitativeFamily.physicalRadius] at hp ⊢
    linarith
  have hx' : ‖x‖ < T.family.radius := (mem_ball_zero_iff.mp hx).trans hpr
  have hη' := (mem_ball.mp hη).trans_le (min_le_left _ _)
  simpa only [PatchQuantitativeFamily.target, AdaptedSection.baseData, covectorCenter,
    map_zero, mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff, dist_self] using
    And.intro hx' (And.intro T.family.radius_pos hη')

private theorem seed_phase_source
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U₀ ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {η : Euclidean (n - 1)}
    (hη : η ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    (0, (0, (0, η))) ∈ (T.currentChart Q).source := by
  have hη' := (mem_ball.mp hη).trans_le (min_le_right _ _)
  have hs' : 0 < 3 * T.family.sourceRadius := mul_pos (by norm_num) T.family.sourceRadius_pos
  have hb : (0, (0, (0, η))) ∈
      ball ((0 : ℝ), T.data.adapted.baseData) (3 * T.family.sourceRadius) := by
    simpa only [AdaptedSection.baseData, covectorCenter, mem_ball,
      Prod.dist_eq, max_lt_iff, dist_self] using ⟨hs', hs', hs', hη'⟩
  have ha := T.family.source_admissible Q hb
  rw [PatchQuantitativeFamily.currentChart,
    restrictChart_source_eq _ _ _ (T.family.source_eq Q)]
  refine ⟨hb, ?_⟩
  change ((T.family.flow Q).position (0, (0, (0, η))), (0, η)) ∈ T.target
  rw [(T.family.flow Q).initial_position _ ha.2, map_zero]
  exact seed_phase_target T (mem_ball_self T.physicalRadius_pos) hη

/-- A fixed label neighborhood and positive primitive frame threshold force
the retained seed's physical covector to be the actual frozen dispersion
graph. The domains precede the seed frame and its later source scale. All
smoothness and the exact seed identity needed by the common conic construction
are conclusions (`new:lem:scaling`, `app:ch_background:eq:bg-Psi`). The origin
hypothesis is supplied by `projectedStress_flatReference_zero`. -/
theorem exists_retained_seed_covector_buffer {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius) :
    ∃ V : Set (Euclidean (n - 1)), IsOpen V ∧
      spatialCarrier T (spectatorCenter z₀, z₀ 0) ∈ V ∧
      V ⊆ ball (covectorCenter T) (2 * T.family.radius) ∧
    ∃ δ > (0 : ℝ), ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U₀ ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ → Q.1 0 = cubeStress n →
      ContDiffOn ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦
        phase (T.currentChart Q).coordinates (p.1, (0, p.2)))
        (ball (0 : Euclidean n) T.physicalRadius ×ˢ V) ∧
      ∀ η ∈ V, gradient (fun x ↦ phase (T.currentChart Q).coordinates (x, (0, η))) 0 =
        (adaptedSliceCoordinates T).equiv.symm (dispersion T η, η) := by
  have hz : z₀ ∈ parameterCube (2 * P.radius) :=
    fun i ↦ (parameterCube_subset_doubledInterior hP.1 (fun j ↦ (hz₀ j).le) i).le
  let ξ := P.toFun z₀
  let ζ₀ := spatialCarrier T (spectatorCenter z₀, z₀ 0)
  have hξ : ξ ≠ 0 := T.data.localReference.covectorSet_nonzero _ (T.data.buffered_mem z₀ hz)
  have hchar : cubeDeterminant ξ = 0 := T.data.buffered_characteristic z₀ hz
  let a : AdaptedSection ξ := {
    normal := T.data.adapted.normal
    embedding := T.data.adapted.embedding
    normal_unit := T.data.adapted.normal_unit
    orthogonal := T.data.adapted.orthogonal
    spanning := T.data.adapted.spanning
    determinant_positive := T.data.localReference.determinantGap_pos.trans_le
      (T.data.localReference.determinant_gap _ (T.data.buffered_mem z₀ hz)) }
  obtain ⟨_, R, _, _, hR, _, hinj⟩ := exists_frozenRootBuffer hξ hchar a
  let V₀ := ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))
  have hζ₀ : ζ₀ ∈ V₀ := by
    have hb := T.patch_buffer z₀ hz
    simpa only [V₀, ζ₀, spatialCarrier, carrierParameters_spectatorCenter,
      PatchQuantitativeFamily.reference, CarrierPhaseReference.spatialPatch,
      AdaptedSection.baseData, covectorCenter, mem_ball, Prod.dist_eq, dist_self,
      max_eq_right dist_nonneg] using hb
  have hV₀ : V₀ ⊆ ball (covectorCenter T) (2 * T.family.radius) :=
    ball_subset_ball ((min_le_left _ _).trans (by linarith [T.family.radius_pos]))
  have href (η : Euclidean (n - 1)) (hη : η ∈ V₀) :
      T.data.localReference.family.chart.chartMomentum (0, (0, η)) =
        T.reference.covector (0, η) := by
    apply chartMomentum_eq_of_phase_linear _ _ T.data.localReference.phase_linear
    apply T.family.reference_target
    exact ball_subset_ball (by linarith [T.family.radius_pos])
      (seed_phase_target T (mem_ball_self T.physicalRadius_pos) hη)
  have hκ : ContinuousOn (fun η ↦ T.reference.covector (0, η)) V₀ := by
    have hs : ContDiffOn ℝ ∞ (fun η ↦
        dispersion T η • T.data.adapted.normal + T.data.adapted.embedding η) V₀ :=
      ((dispersion_smooth T).mono hV₀).smul contDiffOn_const |>.add
        T.data.adapted.embedding.contDiff.contDiffOn
    apply hs.continuousOn.congr
    intro η hη
    exact (FrozenIncidence.reference_covector_eq_graph T (hV₀ hη)).symm
  let V := V₀ ∩ (fun η ↦ T.reference.covector (0, η)) ⁻¹' ball ξ (R / 2)
  have hV : IsOpen V := hκ.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hcenter : T.reference.covector (0, ζ₀) = ξ := by
    change T.reference.covector (0, spatialCarrier T (spectatorCenter z₀, z₀ 0)) = _
    rw [spatialCarrier, carrierParameters_spectatorCenter]
    exact T.reference.patch_covector z₀ (parameterCube_subset_doubledInterior hP.1
      (fun j ↦ (hz₀ j).le))
  obtain ⟨δ, hδ, hclose⟩ := T.family.exists_momentum_comparison_threshold (half_pos hR)
  refine ⟨V, hV, ⟨hζ₀, by
      change T.reference.covector (0, ζ₀) ∈ ball ξ (R / 2)
      rw [hcenter]
      exact mem_ball_self (half_pos hR)⟩,
    inter_subset_left.trans hV₀, δ, hδ, fun Q hQ hQzero ↦ ⟨?_, ?_⟩⟩
  · apply (T.family.phase_smooth Q).comp
      (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    intro p hp
    exact ball_subset_ball (by linarith [T.family.radius_pos]) (seed_phase_target T hp.1 hp.2.1)
  · intro η hη
    let p := (T.currentChart Q).chartMomentum (0, (0, η))
    let p' := T.reference.covector (0, η)
    have ht := seed_phase_target T (mem_ball_self T.physicalRadius_pos) hη.1
    have hs := seed_phase_source T Q hη.1
    have hadm := (T.currentChart Q).source_admissible _ hs
    have hcoords : (T.currentChart Q).coordinates (0, (0, η)) = (0, 0) := by
      simpa only [(T.family.flow Q).initial_position _ hadm.2, map_zero] using
        (T.currentChart Q).left_inverse _ hs
    have hp : p = (T.family.flow Q).momentum (0, (0, (0, η))) := by
      simp only [p, ProjectionChart.chartMomentum, chartLift, hcoords]
    have hpp : p = p' := by
      have hd := (hclose Q hQ (0, (0, η)) (ball_subset_closedBall ht)).1
      change ‖p - T.data.localReference.family.chart.chartMomentum (0, (0, η))‖ < R / 2 at hd
      rw [href η hη.1] at hd
      have hp'ball : p' ∈ ball ξ (R / 2) := hη.2
      apply hinj
      · rw [mem_closedBall]
        exact ((dist_triangle p p' ξ).trans_lt (add_lt_add hd (mem_ball.mp hp'ball))).le.trans
          (by linarith : R / 2 + R / 2 ≤ R)
      · exact (ball_subset_closedBall hp'ball |> closedBall_subset_closedBall (by linarith))
      · apply Prod.ext
        · have he := (T.currentChart Q).eikonal ht
          rw [(T.currentChart Q).gradient_phase_eq_chartMomentum ht,
            normalizedHomogeneousSymbol_h, hQzero] at he
          change (frozenSymbol n).h (0, p) = (frozenSymbol n).h (0, p')
          rw [frozenSymbol_h, frozenSymbol_h]
          have hc := FrozenIncidence.dispersion_characteristic T (hV₀ hη.1)
          rw [FrozenIncidence.reference_covector_eq_graph T (hV₀ hη.1)] at hc
          change cubeDeterminant p' = 0 at hc
          rw [hc, mul_zero]
          simpa only [determinant_cubeStress] using he
        · apply ext_inner_right ℝ
          intro v
          change inner ℝ (T.data.adapted.embedding.toContinuousLinearMap.adjoint p) v =
            inner ℝ (T.data.adapted.embedding.toContinuousLinearMap.adjoint p') v
          rw [reference_covector_adjoint T (hV₀ hη.1), ContinuousLinearMap.adjoint_inner_left,
            hp, ← T.family.section_eq Q]
          exact (T.family.flow Q).initial_momentum _ hadm.2 v
    rw [(T.currentChart Q).gradient_phase_eq_chartMomentum ht]
    change p = _
    rw [hpp]
    apply (adaptedSliceCoordinates T).equiv.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have hc := FrozenIncidence.reference_covector_eq_graph T (hV₀ hη.1)
    change (adaptedSliceCoordinates T).equiv (T.reference.covector (0, η)) = _
    rw [← hc]
    change (physicalCoordinates T (adaptedSpacetime T.data.adapted
      (WithLp.toLp 2 (dispersion T η, η)))).ofLp = _
    rw [physicalCoordinates_adapted]
end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
