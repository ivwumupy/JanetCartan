module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Coordinates
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties

/-!
# The actual zero-energy full phase in adapted coordinates

These are the literal phases consumed by the quotient comparison in
`app:ch_seed:prop:seed-phase-charts`. They restrict `T.currentChart`, preserving
the quantitative family's chart choice. The reference Hamiltonian and its
affine phase identity are derived from the retained frozen flow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts
open HamiltonPhase ActualCarriers ActualCarriers.FrozenPhaseReference
open ActualCarriers.CurrentFullPhase FrozenMenu

namespace ActualPhase
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The fixed center of the spatial-covector chart
(`app:ch_seed:prop:seed-phase-charts`). -/
def covectorCenter : Euclidean (n - 1) :=
  T.data.adapted.embedding.toContinuousLinearMap.adjoint T.data.center

/-- The frozen carrier patch with its first parameter distinguished from
the two spectators (`app:ch_seed:prop:seed-phase-charts`). -/
def spatialCarrier (q : Euclidean 2 × ℝ) : Euclidean (n - 1) :=
  T.reference.spatialPatch (carrierParameters q)

/-- Joint spectator/scalar regularity of the actual frozen spatial patch
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem spatialCarrier_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (spatialCarrier T)
      (carrierParameters ⁻¹' parameterInterior (2 * P.radius)) :=
  (T.reference.spatialPatch_smooth hP).comp carrierParameters.contDiff.contDiffOn
    (fun _ h ↦ h)

/-- The literal current zero-energy phase, with orthogonal physical coordinates
(`app:ch_seed:eq:seed-exact-phase-quotient`). -/
def current (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) : ℝ :=
  phase (T.currentChart Q).coordinates (adaptedPhaseInclusion T.data.adapted q)

/-- The fixed frozen phase, restricted along the identical coordinate map
(`app:ch_seed:prop:seed-phase-charts`). -/
def reference (q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) : ℝ :=
  phase T.reference.chart.coordinates (adaptedPhaseInclusion T.data.adapted q)

/-- The actual frozen scalar dispersion: the normal component of the covector
constructed by the frozen Hamilton flow (`app:ch_seed:prop:seed-phase-charts`). -/
def dispersion (ζ : Euclidean (n - 1)) : ℝ :=
  ⟪T.data.adapted.normal, T.reference.covector (0, ζ)⟫_ℝ

/-- The adapted inclusion maps the whole phase ball to the original full
target ball, with exactly the same radius (`app:lem:common-hamilton-phase`). -/
theorem inclusion_mem_ball {r : ℝ}
    {q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)} :
    adaptedPhaseInclusion T.data.adapted q ∈
        ball (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) r ↔
      q ∈ ball (0, covectorCenter T) r := by
  simp only [mem_ball, adaptedPhaseInclusion_apply, AdaptedSection.baseData,
    covectorCenter, map_zero, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
    dist_zero_right, LinearIsometry.norm_map]

/-- Closed phase construction sets retain their original radius and chart
choice (`app:ch_seed:eq:seed-phase-tame`). -/
theorem inclusion_mem_closedBall {r : ℝ}
    {q : WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)} :
    adaptedPhaseInclusion T.data.adapted q ∈
        closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) r ↔
      q ∈ closedBall (0, covectorCenter T) r := by
  simp only [mem_closedBall, adaptedPhaseInclusion_apply, AdaptedSection.baseData,
    covectorCenter, map_zero, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
    dist_zero_right, LinearIsometry.norm_map]

/-- Joint smoothness of the actual current phase on an open enlargement of
its fixed construction ball (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem current_smooth (Q : _) :
    ContDiffOn ℝ ∞ (current T Q)
      (ball (0, covectorCenter T) (2 * T.family.radius)) := by
  exact (T.family.phase_smooth Q).comp
    (adaptedPhaseInclusion T.data.adapted).contDiff.contDiffOn
    (fun _ h ↦ (inclusion_mem_ball T).mpr h)

private theorem reference_coordinates_smooth :
    ContDiffOn ℝ ∞ T.data.localReference.family.chart.coordinates
      T.data.localReference.family.chart.target := by
  rw [T.data.localReference.family.reference_control.target_eq]
  exact T.data.localReference.family.reference_control.coordinates_smooth

/-- Smoothness of the same retained frozen phase on the doubled phase ball
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem reference_smooth : ContDiffOn ℝ ∞ (reference T)
    (ball (0, covectorCenter T) (2 * T.family.radius)) := by
  exact ((T.data.localReference.family.chart.contDiffOn_phase
    (reference_coordinates_smooth T)).mono T.family.reference_target).comp
      (adaptedPhaseInclusion T.data.adapted).contDiff.contDiffOn
      (fun _ h ↦ (inclusion_mem_ball T).mpr h)

private theorem zero_physical_mem {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (2 * T.family.radius)) :
    ((0 : Euclidean n), ((0 : ℝ), ζ)) ∈ T.data.localReference.family.chart.target := by
  apply T.family.reference_target
  simpa only [mem_ball, AdaptedSection.baseData, map_zero, covectorCenter,
    Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hζ

/-- The frozen covector's tangential projection is the prescribed covector.
This follows from conservation of the actual frozen momentum and the initial
canonical pairing (`app:ch_seed:prop:seed-phase-charts`). -/
theorem reference_covector_adjoint {ζ : Euclidean (n - 1)}
    (hζ : ζ ∈ ball (covectorCenter T) (2 * T.family.radius)) :
    T.data.adapted.embedding.toContinuousLinearMap.adjoint
      (T.reference.covector (0, ζ)) = ζ := by
  let C := T.data.localReference.family.chart
  have hq := zero_physical_mem T hζ
  have he := chartMomentum_eq_of_phase_linear C T.data.localReference.covector
    T.data.localReference.phase_linear hq
  have hs := C.source_admissible _ (C.maps_to_source _ hq)
  change T.data.adapted.embedding.toContinuousLinearMap.adjoint
    (T.data.localReference.covector (0, ζ)) = ζ
  rw [← he]
  change T.data.adapted.embedding.toContinuousLinearMap.adjoint
    (T.data.localReference.family.flow.momentum (chartLift C.coordinates (0, (0, ζ)))) = ζ
  rw [frozenFlow_momentum_eq_initial _ hs.1 hs.2]
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,
    ← T.data.localReference.family.reference_control.section_eq]
  exact T.data.localReference.family.flow.initial_momentum _ hs.2 v

/-- The reference scalar dispersion is smooth, derived from the actual
transported momentum (`app:ch_seed:prop:seed-phase-charts`). -/
theorem dispersion_smooth : ContDiffOn ℝ ∞ (dispersion T)
    (ball (covectorCenter T) (2 * T.family.radius)) := by
  let C := T.data.localReference.family.chart
  have hm := C.contDiffOn_chartMomentum
    T.data.localReference.family.reference_control.momentum_smooth
    (reference_coordinates_smooth T)
  have hs : ContDiffOn ℝ ∞ (fun ζ ↦ C.chartMomentum (0, (0, ζ)))
      (ball (covectorCenter T) (2 * T.family.radius)) :=
    hm.comp (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
      (fun _ h ↦ zero_physical_mem T h)
  apply (contDiffOn_const.inner ℝ hs).congr
  intro ζ hζ
  exact congrArg (fun p ↦ ⟪T.data.adapted.normal, p⟫_ℝ)
    (chartMomentum_eq_of_phase_linear C T.data.localReference.covector
      T.data.localReference.phase_linear (zero_physical_mem T hζ)).symm

/-- The precise frozen formula required by `exists_phaseCharts_c1_comparison`,
proved for the retained reference chart (`app:ch_seed:prop:seed-phase-charts`). -/
theorem reference_eq_affine : EqOn (reference T) (Comparison.referencePhase (dispersion T))
    (ball (0, covectorCenter T) (2 * T.family.radius)) := by
  intro q hq
  have htarget := T.family.reference_target ((inclusion_mem_ball T).mpr hq)
  have hζ : q.2 ∈ ball (covectorCenter T) (2 * T.family.radius) :=
    (mem_ball.mp hq).trans_le' (le_max_right _ _)
  have hadj := reference_covector_adjoint T hζ
  change phase T.data.localReference.family.chart.coordinates
    (adaptedPhaseInclusion T.data.adapted q) = _
  rw [T.data.localReference.phase_linear _ htarget]
  change ⟪T.reference.covector (0, q.2),
    q.1.ofLp.1 • T.data.adapted.normal + T.data.adapted.embedding q.1.ofLp.2⟫_ℝ = _
  have ht : ⟪T.reference.covector (0, q.2), T.data.adapted.embedding q.1.ofLp.2⟫_ℝ =
      ⟪q.2, q.1.ofLp.2⟫_ℝ := by
    change ⟪T.reference.covector (0, q.2),
      T.data.adapted.embedding.toContinuousLinearMap q.1.ofLp.2⟫_ℝ = _
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [inner_add_right, inner_smul_right, ht]
  simp only [Comparison.referencePhase, dispersion, real_inner_comm]

end ActualPhase
end JanetCartan.FullPhaseCharts
