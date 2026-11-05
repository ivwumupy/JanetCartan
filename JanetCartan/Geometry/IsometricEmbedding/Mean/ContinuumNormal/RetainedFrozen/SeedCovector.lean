module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.SeedCovector
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling

/-!
# Uniform exact seed covectors on the original parameter cube

The retained source proof uses the original `D.roots`, with a single frame
threshold before source initialization. Extend the local root-uniqueness proof
to the closed original cube, using the already buffered doubled patch, then
use compactness to make its positive tolerance uniform. No incidence cover,
minor, mask or Hamilton chart is changed.
Consumer: `retained_incidence_spectral_bounds`, hypothesis `hseed`
(`new:lem:scaling`, `app:ch_seed:eq:seed-frozen-detection`).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open CarrierVariation.FamilyInputs
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
theorem exists_seed_covector_buffer_on_parameterCube {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterCube P.radius) :
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
    fun i ↦ (parameterCube_subset_doubledInterior hP.1 hz₀ i).le
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
      hz₀)
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

/-- One primitive frame tolerance makes the retained carrier covector exactly
its original frozen patch at the origin on the entire closed parameter cube.
The tolerance precedes the seed and every subsequent incidence selection.
The actual initialized flat seed supplies `Q 0 = cubeStress n`; its source
contraction supplies the frame tolerance. This closes the covector-identity
input of `retained_incidence_spectral_bounds` without changing `D.roots`
(`new:lem:scaling`, `app:ch_seed:eq:seed-frozen-detection`). -/
theorem exists_uniform_seed_carrierGradient_zero {c C : ℝ} (hP : P.IsValid c C) :
    ∃ δ > (0 : ℝ), ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U₀ ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ → Q.1 0 = cubeStress n →
      ∀ z ∈ parameterCube P.radius, T.carrierGradient Q 0 z = P.toFun z := by
  classical
  choose V hV hcenter hVbuffer δ hδ hlocal using
    fun z : parameterCube P.radius ↦ exists_seed_covector_buffer_on_parameterCube T hP z.property
  let Z (z : parameterCube P.radius) :=
    parameterInterior (2 * P.radius) ∩ T.reference.spatialPatch ⁻¹' V z
  have hZ (z : parameterCube P.radius) : IsOpen (Z z) :=
    (T.reference.spatialPatch_smooth hP).continuousOn.isOpen_inter_preimage
      (isOpen_parameterInterior _) (hV z)
  have hcover : parameterCube P.radius ⊆ ⋃ z : parameterCube P.radius, Z z := by
    intro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, parameterCube_subset_doubledInterior hP.1 hz, ?_⟩
    simpa only [mem_preimage, spatialCarrier, carrierParameters_spectatorCenter] using hcenter ⟨z, hz⟩
  obtain ⟨centers, hcenters⟩ := (isCompact_parameterCube P.radius).elim_finite_subcover
    Z hZ hcover
  obtain ⟨δ₀, hδ₀, hδi⟩ := Pi.exists_forall_pos_add_lt (fun z : centers ↦ hδ z.1)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro Q hQ hQzero z hz
  obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hcenters hz)
  have hη : T.reference.spatialPatch z ∈ V j := hzj.2
  have he := (hlocal j Q (hQ.trans (by simpa using hδi ⟨j, hj⟩)) hQzero).2 _ hη
  change T.carrierGradient Q 0 z = _ at he
  rw [he]
  have href : T.reference.covector (0, T.reference.spatialPatch z) = P.toFun z :=
    T.reference.patch_covector z (parameterCube_subset_doubledInterior hP.1 hz)
  rw [← href]
  apply (adaptedSliceCoordinates T).equiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hc := FrozenIncidence.reference_covector_eq_graph T (hVbuffer j hη)
  rw [← hc]
  change _ = (physicalCoordinates T (adaptedSpacetime T.data.adapted
    (WithLp.toLp 2 (dispersion T (T.reference.spatialPatch z), T.reference.spatialPatch z)))).ofLp
  rw [physicalCoordinates_adapted]


/-- A common tolerance for the supplied finite Hamilton menu, valid for every
actual flat seed admitted on the same physical domain. The origin-frame identity
is proved from `FlatReference`, and the Hamilton admission and exact original
patch covectors are simultaneous conclusions. The initializer may intersect
this tolerance before choosing its seed scale; no new cover or minors are
selected (`new:lem:scaling`, `app:ch_seed:eq:seed-frozen-detection`). -/
theorem exists_flatSeed_incidence_covector_threshold {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C)
    (Tfamily : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U₀ hU₀)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U₀)
    (hball : ∀ i, closedBall (0 : Euclidean n) (Tfamily i).data.localReference.stateRadius ⊆ K) :
    ∃ δ > (0 : ℝ), ∀ (G : FlatReference n)
      (hQ : ContDiffOn ℝ ∞ (ProjectedStressFrame.projectedStress G.map) U₀),
      cNorm K 6 (ProjectedStressFrame.projectedStress G.map - fun _ ↦ cubeStress n) < δ →
      ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (Tfamily i).data.localReference.stateRadius) 6
          (ProjectedStressFrame.projectedStress G.map - fun _ ↦ cubeStress n) <
            (Tfamily i).family.threshold,
      ∀ i z, z ∈ parameterCube (D.patches i.1 i.2).radius →
        (Tfamily i).carrierGradient ⟨ProjectedStressFrame.projectedStress G.map, hQ, hlow i⟩ 0 z =
          (D.patches i.1 i.2).toFun z := by
  classical
  choose δ hδ hseed using fun i ↦
    exists_uniform_seed_carrierGradient_zero (Tfamily i) (hD.2.2.2.2.1 i.1 i.2).1
  obtain ⟨ε, hε, hεi⟩ := Pi.exists_forall_pos_add_lt
    (fun i ↦ lt_min (hδ i) (Tfamily i).family.threshold_pos)
  refine ⟨ε, hε, ?_⟩
  intro G hQ hclose
  have hiε i : ε < min (δ i) (Tfamily i).family.threshold := by simpa using hεi i
  have hsmall i : cNorm (closedBall (0 : Euclidean n)
      (Tfamily i).data.localReference.stateRadius) 6
      (ProjectedStressFrame.projectedStress G.map - fun _ ↦ cubeStress n) < ε :=
    (cNorm_mono_set_of_contDiffAt (hball i) hK (fun x hx ↦
      ((hQ.contDiffAt (hU₀.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp))).trans_lt hclose
  have hlow i := (hsmall i).trans ((hiε i).trans_le (min_le_right _ _))
  refine ⟨hlow, ?_⟩
  intro i z hz
  exact hseed i ⟨ProjectedStressFrame.projectedStress G.map, hQ, hlow i⟩
    ((hsmall i).trans ((hiε i).trans_le (min_le_left _ _)))
    (funext (ProjectedStressFrame.projectedStress_flatReference_zero G)) z hz

end JanetCartan.ContinuumNormal.RetainedFrozen
