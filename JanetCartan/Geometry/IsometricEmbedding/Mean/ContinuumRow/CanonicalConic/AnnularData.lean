module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.LocalCharts
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Comparison

/-!
# Annular data for the actual supported cone

The local projected-stress charts and the stronger primitive transverse
comparison instantiate `ConicChart.AnnularData`. This leaf supplies the
actual annular normalization data used by the joint inverse and Jacobian
proofs. The final constructor discharges these local hypotheses from
`exists_actual_local_charts` and `exists_supported_transverse_threshold`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison CanonicalCarrier
open ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual annular data for the retained Hamilton chart. Local injectivity
and the transverse comparison are supplied by `exists_actual_local_charts` and
`exists_supported_transverse_threshold`; this constructor is used by the smooth
conic extension in `app:ch_background:eq:bg-Psi`. -/
def supportedAnnularData
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r : ℝ} (hr : 0 < r) (p : Euclidean 2 × Euclidean n × Euclidean n)
    (hinj : InjOn (adaptedTransportChart T Q p) (dataBox z₀ ηb (2 * r)))
    (hclose : ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
      ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) :
    AnnularData (Euclidean (n - 1)) where
  map := adaptedTransportChart T Q p
  cone := supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)
  innerRadius := 1 - angularWidth ηb r
  outerRadius := 1 + angularWidth ηb r
  error := angularWidth ηb r / 4
  inner_nonneg := (angularWidth_spec hηb hr).2.2.2.1
  error_nonneg := (angularWidth_spec hηb hr).2.2.2.2.1
  error_lt_one := (angularWidth_spec hηb hr).2.2.2.2.2.1
  inner_buffer := (angularWidth_spec hηb hr).2.2.2.2.2.2.1
  outer_buffer := (angularWidth_spec hηb hr).2.2.2.2.2.2.2
  covector_ne_zero := fun _ hu ↦ hu.2.1
  scale_mem := fun _ hu _ ht ↦ radialScale_mem_supportedCone hu ht
  homogeneous := fun u _ t _ ↦ adaptedTransportChart_radialScale T Q p u t
  transverse_close := hclose
  annular_injective := by
    intro u hu v hv huv
    have hμ : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
    have hbuf := (angularWidth_spec hηb hr).2.2.1.le
    have hu' := annular_dilation_mem_dataSet z₀ hηb hbuf hu.1 hu.2.1 hu.2.2
    have hv' := annular_dilation_mem_dataSet z₀ hηb hbuf hv.1 hv.2.1 hv.2.2
    have hsub : dataSet z₀ ηb r ⊆ dataBox z₀ ηb (2 * r) := by
      exact prod_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    have heq := hinj (hsub hu') (hsub hv') (by
      rw [adaptedTransportChart_radialScale, adaptedTransportChart_radialScale, huv])
    have hh := congrArg (radialScale ‖ηb‖⁻¹) heq
    simpa [hμ.ne'] using hh

end JanetCartan.ContinuumRow.CanonicalConic
