module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.ChartCutoff

/-!
# The fixed-cutoff scalar, flow and geometric normal extensions

These definitions specify the actual functions whose global profiles feed
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`. They preserve
the prescribed initial scalar, the unit-initial exponential factor and the
scalar-free geometric normal near the complete original mask support.
All cutoffs precede the immersion and initial scalar.

Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ}

/-- The original initial scalar extended using a bump strictly inside its
original `R / 8` norm domain, then relabeled into the literal adjoint variables
(`app:ch_background:prop:bg-adjoint`). -/
def extendedInitialScalar (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) : CarrierVariable n → ℝ :=
  initialScalar (fun q ↦ initialBump z₀ hR q * initial q)

/-- Global smoothness of the initial extension from smoothness on the
original initial ball; the cutoff support is strictly inside that ball
(`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_contDiff (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8))) :
    ContDiff ℝ ∞ (extendedInitialScalar z₀ hR initial) := by
  have hh : ContDiff ℝ ∞ (fun q ↦ initialBump z₀ hR q * initial q) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood isOpen_ball
      ((initialBump z₀ hR).contDiff.contDiffOn.mul hi)
      (tsupport_mul_subset_left.trans (initialBump_tsupport_subset z₀ hR))
  exact hh.comp (contDiff_snd.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_fst))

/-- The initial extension agrees with the original scalar on a neighborhood
of each point in its fixed footpoint buffer. `InitialBuffer` proves that the
actual supported footpoints belong to this buffer
(`app:ch_background:prop:bg-adjoint`). -/
theorem extendedInitialScalar_eventuallyEq (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) {p : CarrierVariable n}
    (hp : (p.2, CanonicalCarrier.parameter p.1) ∈
      ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    extendedInitialScalar z₀ hR initial =ᶠ[𝓝 p] initialScalar initial := by
  have hh := (initialBump_eventuallyEq_one z₀ hR hp).comp_tendsto
    (continuous_snd.prodMk (CanonicalCarrier.parameter.continuous.comp
      continuous_fst)).continuousAt
  filter_upwards [hh] with q hq
  change initialBump z₀ hR (q.2, CanonicalCarrier.parameter q.1) *
    initial (q.2, CanonicalCarrier.parameter q.1) = initial (q.2, CanonicalCarrier.parameter q.1)
  rw [show initialBump z₀ hR (q.2, CanonicalCarrier.parameter q.1) = 1 from hq, one_mul]

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Compact extension of the literal unit-initial flow factor. The cutoff is
fixed independently of the flow and the current immersion
(`app:ch_background:prop:bg-adjoint`). -/
def extendedFlowFactor (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) (p : CarrierParameter × Euclidean n) : ℝ :=
  chartBump z₀ ha (p.2, p.1) * flowFactor T Q F row col Φ Y p

/-- Compact extension of the geometric normal, before the prescribed scalar
and its flow factor are inserted (`app:ch_background:eq:bg-T`). -/
def extendedGeometricNormal (F : Euclidean n → Euclidean N) (col : Fin n)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    (p : CarrierParameter × Euclidean n) : Euclidean N :=
  chartBump z₀ ha (p.2, p.1) • geometricNormal T Q F col p

/-- Exact neighborhood agreement of the extended and original unit-initial
flow on the entire supported chart (`app:ch_background:prop:bg-adjoint`). -/
theorem extendedFlowFactor_eventuallyEq (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) {p : CarrierParameter × Euclidean n}
    (hp : (p.2, p.1) ∈ supportedChart z₀ a) :
    extendedFlowFactor T Q F row col Φ Y z₀ ha =ᶠ[𝓝 p]
      flowFactor T Q F row col Φ Y := by
  have hh := (chartBump_eventuallyEq_one z₀ ha hp).comp_tendsto continuous_swap.continuousAt
  filter_upwards [hh] with q hq
  change chartBump z₀ ha (q.2, q.1) * flowFactor T Q F row col Φ Y q = _
  rw [show chartBump z₀ ha (q.2, q.1) = 1 from hq, one_mul]

/-- Exact neighborhood agreement of the extended and original geometric
normal on the entire supported chart (`app:ch_background:eq:bg-T`). -/
theorem extendedGeometricNormal_eventuallyEq (F : Euclidean n → Euclidean N) (col : Fin n)
    (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a) {p : CarrierParameter × Euclidean n}
    (hp : (p.2, p.1) ∈ supportedChart z₀ a) :
    extendedGeometricNormal T Q F col z₀ ha =ᶠ[𝓝 p] geometricNormal T Q F col := by
  have hh := (chartBump_eventuallyEq_one z₀ ha hp).comp_tendsto continuous_swap.continuousAt
  filter_upwards [hh] with q hq
  change chartBump z₀ ha (q.2, q.1) • geometricNormal T Q F col q = _
  rw [show chartBump z₀ ha (q.2, q.1) = 1 from hq, one_smul]

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
