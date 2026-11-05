module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.ChartGrades
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Derivatives
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.Setup
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes

/-!
# The canonical phase on the raw physical slices

These identities connect the SAME retained Hamilton phase to the phase of
`SliceBounds.exists_rawPhysicalSliceSobolev_wkbGrades` and to the transverse
charts of `app:ch_seed:prop:seed-phase-charts`. The identities include epsilon
zero. No phase, inverse geometry, or amplitude is chosen in this module.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts FullPhaseCharts.ActualPhase
open FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

/-- The original full phase pulled back by the consumer's actual adapted
coordinates (`app:ch_waves:eq:individual-raw-slice`). -/
def canonicalBasePhase (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (q : ℝ × E) (η : E) : ℝ :=
  LeadingWave.FullModulation.phase T Q (adaptedPhysicalCoordinates T.data.adapted q) η

/-- The canonical raw slice phase, with its integral value at zero. This is
literally the phase required by the WKB slice consumer
(`app:ch_seed:eq:seed-quotient-integral`, `app:ch_waves:eq:individual-raw-slice`). -/
def canonicalSlicePhase (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z : Euclidean 3) (t ε : ℝ) (y η : E) : ℝ :=
  rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
    (ε, (t, y), η)

/-- Exact identification with the published current phase in Hilbert adapted
coordinates (`app:ch_seed:prop:seed-phase-charts`). -/
theorem canonicalBasePhase_eq_current (Q : _) (q : ℝ × E) (η : E) :
    canonicalBasePhase T Q q η = current T Q (WithLp.toLp 2 q, η) := rfl

/-- The phase equality supplied to the raw slice consumer holds for every
epsilon, including zero (`app:ch_waves:eq:individual-raw-slice`). -/
theorem canonicalSlicePhase_eq_rawSlicePhaseExtension (Q : _) (z : Euclidean 3)
    (t ε : ℝ) (y η : E) :
    canonicalSlicePhase T Q z t ε y η = rawSlicePhaseExtension
      (fun q ξ ↦ LeadingWave.FullModulation.phase T Q
        (adaptedPhysicalCoordinates T.data.adapted q) ξ)
      (T.reference.spatialPatch z) (ε, (t, y), η) := rfl

/-- The zero-epsilon value is the covector differential of the SAME full
phase, not an independently prescribed limiting phase
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem canonicalSlicePhase_zero (Q : _) (z : Euclidean 3) (t : ℝ) (y η : E) :
    canonicalSlicePhase T Q z t 0 y η =
      fderiv ℝ (LeadingWave.FullModulation.phase T Q
        (adaptedPhysicalCoordinates T.data.adapted (t, y)))
        (T.reference.spatialPatch z) η := by
  simp only [canonicalSlicePhase, rawSlicePhaseExtension, phaseShiftQuotient_zero,
    inner_gradient_left]
  rfl

/-- The literal transverse modulation phase of the full-chart construction
is this raw slice phase at every epsilon
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem canonicalSlicePhase_eq_modulationPhase (Q : _) (z : Euclidean 3)
    (t ε : ℝ) (y η : E) :
    canonicalSlicePhase T Q z t ε y η =
      Comparison.modulationPhase
        (fun q : E × E ↦ current T Q (WithLp.toLp 2 (t, q.1), q.2))
        (spatialCarrier T) ε (spectatorCenter z) (z 0, η) y := by
  simp only [canonicalSlicePhase, rawSlicePhaseExtension, Comparison.modulationPhase,
    spatialCarrier, carrierParameters_spectatorCenter]
  rfl

/-- The normal-comparison averaged gradient is exactly the published
transverse chart. This is an identity of the actual integral definitions,
including epsilon zero (`app:ch_seed:prop:seed-phase-charts`). -/
theorem averagedGradient_canonicalSlicePhase (Q : _) (z : Euclidean 3)
    (t ε : ℝ) (x y η : E) :
    NormalComparison.averagedGradient (canonicalSlicePhase T Q z t ε) x y η =
      transverseChartFamily (current T Q) (spatialCarrier T)
        (ε, spectatorCenter z, t, z 0, x, y) η := by
  have hp : (fun v ↦ canonicalSlicePhase T Q z t ε v η) =
      Comparison.modulationPhase
        (fun q : E × E ↦ current T Q (WithLp.toLp 2 (t, q.1), q.2))
        (spatialCarrier T) ε (spectatorCenter z) (z 0, η) :=
    funext fun v ↦ canonicalSlicePhase_eq_modulationPhase T Q z t ε v η
  unfold NormalComparison.averagedGradient NormalComparison.averagedPhaseDifferential
  calc
    _ = ∫ s in (0 : ℝ)..1,
        gradient (fun v ↦ canonicalSlicePhase T Q z t ε v η) (y + s • (x - y)) :=
      ((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.intervalIntegral_comp_comm
        (a := (0 : ℝ)) (b := 1) (μ := volume)
        (fun s : ℝ ↦ fderiv ℝ (fun v ↦ canonicalSlicePhase T Q z t ε v η)
          (y + s • (x - y)))).symm
    _ = _ := by simp only [hp]; rfl

/-- Joint smoothness of the unshifted canonical phase on the original full
phase ball, pulled back by the consumer's coordinates
(`app:ch_waves:setup:oscillatory`). -/
theorem canonicalBasePhase_smooth (Q : _) :
    ContDiffOn ℝ ∞ (Function.uncurry (canonicalBasePhase T Q))
      ((adaptedPhysicalCoordinates T.data.adapted ⁻¹'
        ball 0 (2 * T.family.radius)) ×ˢ ball (covectorCenter T) (2 * T.family.radius)) := by
  apply (LeadingWave.FullModulation.phase_smooth T Q).comp
    (((NullTransport.ActualFlow.adaptedCoordinates T.data.adapted).symm.contDiff.comp
      contDiff_fst).prodMk contDiff_snd).contDiffOn
  intro q hq
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨hq.1, hq.2⟩

/-- At nonzero epsilon the canonical slice phase is the actual divided
full-phase difference, on its original buffered covector segment
(`app:ch_seed:eq:seed-exact-phase-quotient`). -/
theorem canonicalSlicePhase_eq_div (Q : _) (z : Euclidean 3)
    {t ε : ℝ} {y η : E}
    (hx : adaptedPhysicalCoordinates T.data.adapted (t, y) ∈
      ball 0 (2 * T.family.radius)) (hε : ε ≠ 0)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1,
      T.reference.spatialPatch z + (s * ε) • η ∈
        ball (covectorCenter T) (2 * T.family.radius)) :
    canonicalSlicePhase T Q z t ε y η =
      (LeadingWave.FullModulation.phase T Q
          (adaptedPhysicalCoordinates T.data.adapted (t, y))
          (T.reference.spatialPatch z + ε • η) -
        LeadingWave.FullModulation.phase T Q
          (adaptedPhysicalCoordinates T.data.adapted (t, y))
          (T.reference.spatialPatch z)) / ε := by
  exact rawSlicePhaseExtension_eq_rawPrimaryPhaseDifference isOpen_ball
    (canonicalBasePhase_smooth T Q) hx hε hseg

/-- The canonical Hamilton initial value in the exact adapted coordinates
used by the raw operator (`app:ch_waves:thm:leading`). -/
theorem canonicalBasePhase_initial (Q : _) {y η : E}
    (hy : ‖y‖ < T.physicalRadius)
    (hη : η ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    canonicalBasePhase T Q (0, y) η = ⟪y, η⟫_ℝ := by
  simpa only [canonicalBasePhase, adaptedPhysicalCoordinates_apply, zero_smul, zero_add]
    using LeadingWave.FullModulation.phase_initial_value T Q hy hη

/-- The canonical initial identity also identifies the covector derivative,
on the original open source buffer (`app:ch_waves:thm:leading`). -/
theorem canonicalBasePhase_initial_fderiv (Q : _) {y η : E}
    (hy : ‖y‖ < T.physicalRadius)
    (hη : η ∈ ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    fderiv ℝ (canonicalBasePhase T Q (0, y)) η = innerSL ℝ y := by
  have he : canonicalBasePhase T Q (0, y) =ᶠ[𝓝 η] (innerSL ℝ y : E → ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hη] with ξ hξ
    exact canonicalBasePhase_initial T Q hy hξ
  rw [he.fderiv_eq, ContinuousLinearMap.fderiv]

/-- At initial time the actual raw slice phase is the transverse pairing
for every epsilon whose entire segment lies in the original source buffer.
In particular this covers zero epsilon with no division argument
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:thm:leading`). -/
theorem canonicalSlicePhase_initial (Q : _) (z : Euclidean 3)
    {ε : ℝ} {y η : E} (hy : ‖y‖ < T.physicalRadius)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1,
      T.reference.spatialPatch z + (s * ε) • η ∈
        ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius))) :
    canonicalSlicePhase T Q z 0 ε y η = ⟪y, η⟫_ℝ := by
  unfold canonicalSlicePhase rawSlicePhaseExtension phaseShiftQuotient
  simp only [inner_gradient_left]
  calc
    _ = ∫ _s in (0 : ℝ)..1, ⟪y, η⟫_ℝ := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [canonicalBasePhase_initial_fderiv T Q hy (hseg s (by simpa using hs))]
      rfl
    _ = _ := by simp

end JanetCartan.RawPrimary.SliceGeometry
