module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SliceCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.FrequencySupport

/-!
# The full sampling phase in the actual coordinates

Identify the SAME integral modulation quotient at every epsilon, including
zero, with the averaged gradient used by `FrequencySupport`. Both physical
positions and both unchanged spectators are retained. The input coordinates
are the existing volume-preserving `CanonicalConic.adaptedSliceCoordinates`.
The consumer is the supported annulus in `app:ch_seed:eq:seed-normal-annulus`,
used after `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius Topology

namespace JanetCartan.Sampling.MeanNormalBound.CanonicalGap
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison
open ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The literal full quotient in the physical and normalized input variables
of `UniformNormalData.phase`, with the two spectators fixed, not discarded
(`app:ch_seed:eq:seed-exact-phase-quotient`). -/
def normalizedFullPhase (v : Euclidean 2) (ε : ℝ) (x u : Euclidean n) : ℝ :=
  modulation T Q ((carrierParameters (v, ((adaptedSliceCoordinates T).equiv u).1),
    ((adaptedSliceCoordinates T).equiv u).2), ε) (physicalCoordinates T x)

/-- The actual quotient and the released full chart use exactly the same
incidence coordinate, covector and spectators, for all epsilon
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem normalizedFullPhase_eq_comparison (v : Euclidean 2) (ε : ℝ)
    (x u : Euclidean n) :
    normalizedFullPhase T Q v ε x u =
      Comparison.modulationPhase (current T Q) (spatialCarrier T) ε v
        ((adaptedSliceCoordinates T).equiv u) (physicalCoordinates T x) := rfl

/-- Pull back both physical positions by the SAME orthogonal chart, leaving
epsilon and the spectators unchanged (`app:ch_seed:prop:seed-phase-charts`). -/
def fullPhaseParameters (ε : ℝ) (v : Euclidean 2) (x y : Euclidean n) :
    ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
      WithLp 2 (ℝ × Euclidean (n - 1)) :=
  (ε, v, physicalCoordinates T x, physicalCoordinates T y)

/-- Orthogonal conjugacy of the full, possibly nonzero-epsilon gradient.
Total derivatives agree even outside the smooth chart; no regularity premise
or replacement by transport is used (`app:ch_seed:eq:seed-normal-annulus`). -/
theorem gradient_normalizedFullPhase (v : Euclidean 2) (ε : ℝ) (x u : Euclidean n) :
    physicalCoordinates T (gradient (fun y ↦ normalizedFullPhase T Q v ε y u) x) =
      gradient (Comparison.modulationPhase (current T Q) (spatialCarrier T) ε v
        ((adaptedSliceCoordinates T).equiv u)) (physicalCoordinates T x) := by
  let e := physicalCoordinates T
  let f := Comparison.modulationPhase (current T Q) (spatialCarrier T) ε v
    ((adaptedSliceCoordinates T).equiv u)
  change e (gradient (f ∘ e) x) = gradient f (e x)
  apply ext_inner_right ℝ
  intro w
  rw [e.inner_map_eq_flip, inner_gradient_left, inner_gradient_left]
  have hd : fderiv ℝ (f ∘ e) x =
      (fderiv ℝ f (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap :=
    e.toContinuousLinearEquiv.comp_right_fderiv
  rw [hd]
  change (fderiv ℝ f (e x)) (e (e.symm w)) = (fderiv ℝ f (e x)) w
  rw [e.apply_symm_apply]

/-- The dual-integral definition in `NormalComparison` is the literal full
chart, with both endpoints and the original input preserved. Isometries commute
with the total integral without an extra integrability assumption
(`app:ch_osc:eq:osc-exact-normal-kernel`, `app:ch_seed:eq:seed-normal-annulus`). -/
theorem averagedGradient_normalizedFullPhase (v : Euclidean 2) (ε : ℝ)
    (x y u : Euclidean n) :
    (physicalCoordinates T (averagedGradient (normalizedFullPhase T Q v ε) x y u)).ofLp =
      fullChartFamily (current T Q) (spatialCarrier T)
        (fullPhaseParameters T ε v x y) ((adaptedSliceCoordinates T).equiv u) := by
  have hi := (InnerProductSpace.toDual ℝ (Euclidean n)).symm.toLinearIsometry.intervalIntegral_comp_comm
      (fun t : ℝ ↦ fderiv ℝ (fun z ↦ normalizedFullPhase T Q v ε z u)
        (y + t • (x - y))) (a := 0) (b := 1) (μ := MeasureTheory.volume)
  have he : averagedGradient (normalizedFullPhase T Q v ε) x y u =
      ∫ t in (0 : ℝ)..1, gradient (fun z ↦ normalizedFullPhase T Q v ε z u)
        (y + t • (x - y)) := hi.symm
  have hc : (∫ t in (0 : ℝ)..1, physicalCoordinates T
      (gradient (fun z ↦ normalizedFullPhase T Q v ε z u) (y + t • (x - y)))) =
      physicalCoordinates T (∫ t in (0 : ℝ)..1,
        gradient (fun z ↦ normalizedFullPhase T Q v ε z u) (y + t • (x - y))) :=
    (physicalCoordinates T).toLinearIsometry.intervalIntegral_comp_comm _
  rw [he, ← hc]
  simp_rw [gradient_normalizedFullPhase T Q]
  simp only [map_add, map_smul, map_sub]
  rfl

/-- The product-coordinate annular lower bound transfers to the physical
Euclidean norm with constant one (`app:ch_seed:eq:seed-normal-annulus`). -/
theorem fullChart_norm_le_averagedGradient (v : Euclidean 2) (ε : ℝ)
    (x y u : Euclidean n) :
    ‖fullChartFamily (current T Q) (spatialCarrier T)
        (fullPhaseParameters T ε v x y) ((adaptedSliceCoordinates T).equiv u)‖ ≤
      ‖averagedGradient (normalizedFullPhase T Q v ε) x y u‖ := by
  rw [← averagedGradient_normalizedFullPhase,
    ← (physicalCoordinates T).norm_map (averagedGradient _ x y u)]
  exact max_le (WithLp.norm_fst_le ℝ _) (WithLp.norm_snd_le ℝ _)

omit Q in
/-- Closed physical/spectator support boxes and the entire closed epsilon
interval lie inside the open buffered parameter chart
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullPhaseParameters_mem {z₀ : Euclidean 3} {s e ε : ℝ}
    (hs : 0 < s) (he : 0 < e) (hε : ε ∈ Icc 0 e)
    {v : Euclidean 2} (hv : v ∈ closedBall (spectatorCenter z₀) (s / 2))
    {x y : Euclidean n} (hx : x ∈ closedBall 0 (s / 2))
    (hy : y ∈ closedBall 0 (s / 2)) :
    fullPhaseParameters T ε v x y ∈ fullParameterSet z₀ s (2 * e) := by
  change (ε, v, physicalCoordinates T x, physicalCoordinates T y) ∈
    fullParameterSet z₀ s (2 * e)
  refine ⟨⟨by linarith [hε.1], by linarith [hε.2]⟩,
    closedBall_subset_ball (by linarith) hv, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using
      closedBall_subset_ball (show s / 2 < s by linarith) hx
  · simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using
      closedBall_subset_ball (show s / 2 < s by linarith) hy

/-- Local identification suffices: a chosen phase extension need only agree
with the full quotient on the physical open ball, at the supported input.
This is the exact phase-identification obligation for the parent's
`UniformNormalData`, not a hypothesis about an inverse amplitude or its gap
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem averagedGradient_eq_of_phase_eqOn
    (φ : Euclidean n → Euclidean n → ℝ) (v : Euclidean 2) (ε : ℝ)
    {s : ℝ} {x y u : Euclidean n}
    (hx : x ∈ ball 0 s) (hy : y ∈ ball 0 s)
    (hφ : EqOn (fun z ↦ φ z u) (fun z ↦ normalizedFullPhase T Q v ε z u)
      (ball 0 s)) :
    averagedGradient φ x y u =
      averagedGradient (normalizedFullPhase T Q v ε) x y u := by
  unfold averagedGradient averagedPhaseDifferential
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hm : y + t • (x - y) ∈ ball 0 s :=
    (convex_ball _ _).add_smul_sub_mem hy hx (by simpa using ht)
  have he : (fun z ↦ φ z u) =ᶠ[𝓝 (y + t • (x - y))]
      (fun z ↦ normalizedFullPhase T Q v ε z u) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hm) hφ
  exact he.fderiv_eq

omit Q in
/-- The actual Hamilton producer identifies the integral phase with the
nonzero full difference quotient on one fixed epsilon neighborhood. This is
the phase producer for the sampling adapter; `rmax` and `emax` can be capped
before calling the supported chart theorem
(`app:ch_seed:eq:seed-exact-phase-quotient`). -/
theorem exists_normalizedFullPhase_quotient_radius {c C : ℝ} (hP : P.IsValid c C)
    {M : ℝ} (hM : 0 < M) :
    ∃ e > (0 : ℝ), ∀ Q, ∀ v ε x u,
      carrierParameters (v, ((adaptedSliceCoordinates T).equiv u).1) ∈
        parameterInterior (3 * P.radius / 2) →
      ‖((adaptedSliceCoordinates T).equiv u).2‖ < M →
      ε ∈ Ioo (-e) e → ε ≠ 0 → x ∈ ball 0 T.family.radius →
      normalizedFullPhase T Q v ε x u =
        (HamiltonPhase.phase (T.currentChart Q).coordinates
          (x, (0, spatialCarrier T (v, ((adaptedSliceCoordinates T).equiv u).1) +
            ε • ((adaptedSliceCoordinates T).equiv u).2)) -
          HamiltonPhase.phase (T.currentChart Q).coordinates
            (x, (0, spatialCarrier T (v, ((adaptedSliceCoordinates T).equiv u).1)))) / ε := by
  obtain ⟨e, he, hall⟩ := exists_smooth_modulation T hP hM
  refine ⟨e, he, ?_⟩
  intro Q v ε x u hz hu hε hne hx
  have hp := (hall Q).2.1
    (carrierParameters (v, ((adaptedSliceCoordinates T).equiv u).1),
      ((adaptedSliceCoordinates T).equiv u).2)
    ⟨hz, by simpa only [mem_ball, dist_zero_right] using hu⟩ ε hε hne
    (physicalCoordinates T x)
    (by simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx)
  simpa only [normalizedFullPhase, current_physicalCoordinates, spatialCarrier] using hp

end JanetCartan.Sampling.MeanNormalBound.CanonicalGap
