module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Basic

/-!
# Phase agreement on every point of the working conic domain

The input here is exactly the agreement on `supportedChart` published by
`PhaseExtension.exists_projected_supported_phase_inputs`. The restriction in
`normalChart` makes that agreement sufficient for the whole-domain `hphase`
of `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`, without a mask
nonvanishing hypothesis (`app:ch_background:eq:bg-Psi`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r aOuter aPhase : ℝ}

local notation "g" => normalChart T Q z₀ ηb r aOuter aPhase

/-- The extended phase has the literal averaged-gradient identity at EVERY
point of the restricted domain. Agreement is on the fixed complete chart,
not just at nonzero masks (`app:ch_background:eq:bg-Psi`). -/
theorem normalChart_phase_identity {c C : ℝ} (hP : P.IsValid c C)
    (hr : 0 < r) (haR : aOuter < T.family.radius) (har : aOuter ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (hY : EqOn Y (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ aPhase))
    (x y : Euclidean n) (v : Euclidean 2) (w : Euclidean n)
    (hw : w ∈ (g).domain x y v) :
    phase Y (TransportKernel.chartCarrierVariable (g).coordinates v w).1 x
        (TransportKernel.chartCarrierVariable (g).coordinates v w).2 -
      phase Y (TransportKernel.chartCarrierVariable (g).coordinates v w).1 y
        (TransportKernel.chartCarrierVariable (g).coordinates v w).2 =
      inner ℝ (x - y) ((g).forward x y v w) := by
  have hx := hY (interior_subset hw.2.1)
  have hy := hY (interior_subset hw.2.2)
  change inner ℝ (Y ((kernelInput T x y v w).1.1, (kernelInput T x y v w).2.1)) _ -
    inner ℝ (Y ((kernelInput T x y v w).1.2, (kernelInput T x y v w).2.1)) _ = _
  rw [hx, hy]
  exact phase_identity_on_symbolInputDomain T Q hP hr haR har hcarrier hw.1

/-- The exact whole-domain phase premise for the data passed to the raw
scalar-transport endpoint, retaining its original detector and masks
(`app:ch_background:prop:bg-adjoint`). -/
theorem normalChart_scalarTransportData_phase_identity {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (hr : 0 < r) (haR : aOuter < T.family.radius) (har : aOuter ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (d : CarrierData n N) (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (scalar : CarrierVariable n → ℝ) (flow : AdjointJetPoint n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N)
    (hY : EqOn Y (CanonicalCarrier.transportPosition T Q) (supportedChart z₀ aPhase)) :
    ∀ x y v w, w ∈ (g).domain x y v →
      carrierChartPhase (scalarTransportData d Y scalar flow ν)
          (TransportKernel.chartCarrierVariable (g).coordinates v w).1 x
          (TransportKernel.chartCarrierVariable (g).coordinates v w).2 -
        carrierChartPhase (scalarTransportData d Y scalar flow ν)
          (TransportKernel.chartCarrierVariable (g).coordinates v w).1 y
          (TransportKernel.chartCarrierVariable (g).coordinates v w).2 =
        inner ℝ (x - y) ((g).forward x y v w) :=
  normalChart_phase_identity T Q hP hr haR har hcarrier Y hY

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
