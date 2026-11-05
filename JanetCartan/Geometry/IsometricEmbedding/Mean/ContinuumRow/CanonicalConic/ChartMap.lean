module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.ProjectedAssembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart

/-!
# Actual local charts for the canonical physical carrier

Instantiate the projected-stress full-phase producer for the SAME retained
Hamilton family as `CanonicalCarrier.transportPosition`. The zero-epsilon
chart is pulled back to the original physical positions. Its positive radius
can lie below any prescribed outer cap, so phase, amplitude and image domains
can be intersected before choosing the immersion.

These are local buffered charts. Extending them to the supported cone and
building the kernel substitution remain separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Original physical positions and the two unchanged spectators at zero
modulation (`app:ch_background:eq:bg-Psi`). -/
def phaseParameters (p : Euclidean 2 × Euclidean n × Euclidean n) :
    ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
      WithLp 2 (ℝ × Euclidean (n - 1)) :=
  (0, p.1, physicalCoordinates T p.2.1, physicalCoordinates T p.2.2)

/-- Joint smoothness of the fixed orthogonal coordinate relabeling
(`app:ch_background:eq:bg-Psi`). -/
theorem phaseParameters_smooth : ContDiff ℝ ∞ (phaseParameters T) :=
  contDiff_const.prodMk (contDiff_fst.prodMk
    (((physicalCoordinates T).contDiff.comp contDiff_snd.fst).prodMk
      ((physicalCoordinates T).contDiff.comp contDiff_snd.snd)))

/-- The open physical/spectator domain used for both positions
(`app:ch_background:eq:bg-Psi`). -/
def physicalParameterSet (z₀ : Euclidean 3) (r : ℝ) :
    Set (Euclidean 2 × Euclidean n × Euclidean n) :=
  ball (spectatorCenter z₀) r ×ˢ ball 0 r ×ˢ ball 0 r

/-- The original-position parameter domain is open
(`app:ch_background:eq:bg-Psi`). -/
theorem physicalParameterSet_open (z₀ : Euclidean 3) (r : ℝ) :
    IsOpen (physicalParameterSet (n := n) z₀ r) :=
  isOpen_ball.prod (isOpen_ball.prod isOpen_ball)

/-- Orthogonal physical coordinates preserve the actual radius buffer
(`app:ch_background:eq:bg-Psi`). -/
theorem phaseParameters_mem {z₀ : Euclidean 3} {r s e : ℝ} (he : 0 < e)
    (hrs : r ≤ s) {p : Euclidean 2 × Euclidean n × Euclidean n}
    (hp : p ∈ physicalParameterSet z₀ r) :
    phaseParameters T p ∈ fullParameterSet z₀ s e := by
  change (0, p.1, physicalCoordinates T p.2.1, physicalCoordinates T p.2.2) ∈
    fullParameterSet z₀ s e
  refine ⟨⟨by linarith, he⟩, ball_subset_ball hrs hp.1, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using
      ball_subset_ball hrs hp.2.1
  · simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using
      ball_subset_ball hrs hp.2.2

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Literal physical averaged gradient, expressed in the retained orthogonal
output coordinates (`app:ch_background:eq:bg-Psi`). -/
def adaptedTransportChart (p : Euclidean 2 × Euclidean n × Euclidean n)
    (u : ℝ × Euclidean (n - 1)) : ℝ × Euclidean (n - 1) :=
  (physicalCoordinates T (transportAveragedGradient (transportPosition T Q)
    ((p.2.1, p.2.2), (u.1, p.1), u.2))).ofLp

/-- Exact identity with the actual full-phase chart, including both positions
and the original spectator (`app:ch_background:eq:bg-Psi`). -/
theorem adaptedTransportChart_eq (p : Euclidean 2 × Euclidean n × Euclidean n)
    (u : ℝ × Euclidean (n - 1)) :
    adaptedTransportChart T Q p u =
      fullChartFamily (current T Q) (spatialCarrier T) (phaseParameters T p) u :=
  transportAveragedGradient_eq_fullChart T Q _

/-- Positive homogeneity follows from the literal covector-linear phase;
the incidence and spectator coordinates are fixed (`app:ch_background:eq:bg-Psi`). -/
theorem adaptedTransportChart_radialScale (p : Euclidean 2 × Euclidean n × Euclidean n)
    (u : ℝ × Euclidean (n - 1)) (t : ℝ) :
    adaptedTransportChart T Q p (ContinuumNormalReduction.ConicChart.radialScale t u) =
      t • adaptedTransportChart T Q p u := by
  change (physicalCoordinates T (transportAveragedGradient (transportPosition T Q)
    (scaleInput t ((p.2.1, p.2.2), (u.1, p.1), u.2)))).ofLp = _
  rw [transportAveragedGradient_smul, map_smul, WithLp.ofLp_smul]
  rfl

/-- Pulling back parameters does not choose a different inverse branch
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem phaseChartInverse_adaptedTransportChart (D : Set (ℝ × Euclidean (n - 1)))
    (p : Euclidean 2 × Euclidean n × Euclidean n) (v : ℝ × Euclidean (n - 1)) :
    phaseChartInverse (adaptedTransportChart T Q) D p v =
      phaseChartInverse (fullChartFamily (current T Q) (spatialCarrier T)) D
        (phaseParameters T p) v := by
  unfold phaseChartInverse
  congr 1
  funext u
  exact adaptedTransportChart_eq T Q p u

end JanetCartan.ContinuumRow.CanonicalConic
