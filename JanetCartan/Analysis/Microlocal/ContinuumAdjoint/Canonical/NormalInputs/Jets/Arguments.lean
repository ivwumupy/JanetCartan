module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Jets.Rescaling

/-!
# Jets of the unchanged amplitude arguments

All positive jets of the original carrier and left/right amplitude argument
maps are uniformly bounded by their fixed linear operator norms. The budget
precedes the varying geometry and every frequency scale.

Consumer: the last three fields of `PrimitiveJetGeometry` for
`app:ch_background:prop:bg-adjoint` and `bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open CanonicalConic ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private def normalCarrierLinear : JointVariables n →L[ℝ] CarrierVariable n :=
  (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n) (CarrierVariable n)).comp
    (jointInputCoordinates T).toContinuousLinearMap

private def normalArgumentsLinear
    (π : Euclidean n × Euclidean n →L[ℝ] Euclidean n) :
    JointVariables n →L[ℝ] AmplitudeVariables n :=
  let c := normalCarrierLinear T
  let x := π.comp ((ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n)
    (CarrierVariable n)).comp (jointInputCoordinates T).toContinuousLinearMap)
  ((ContinuousLinearMap.fst ℝ CarrierParameter (Euclidean (n - 1))).comp c).prod
    (x.prod ((ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean (n - 1))).comp c))

/-- Fixed coordinate jets of the actual normal chart, at every point and
every positive order. No inverse or geometric jet is used here. This supplies
`carrier_jets`, `left_jets`, and `right_jets` of `PrimitiveJetGeometry`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_normalChart_argument_jet_bound :
    ∃ B ≥ (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r aOuter aPhase : ℝ)
      (p : JointVariables n) (j : ℕ), 1 ≤ j →
      let g := normalChart T Q z₀ ηb r aOuter aPhase
      ‖iteratedFDeriv ℝ j g.carrier p‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j g.leftArguments p‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j g.rightArguments p‖ ≤ B := by
  let C := normalCarrierLinear T
  let X := normalArgumentsLinear T (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n))
  let Y := normalArgumentsLinear T (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n))
  refine ⟨‖C‖ + ‖X‖ + ‖Y‖, by positivity, ?_⟩
  intro Q z₀ ηb r aOuter aPhase p j hj
  have hc := NormalComparison.InverseChartJet.norm_iteratedFDeriv_linear_pos_le C p hj
  have hx := NormalComparison.InverseChartJet.norm_iteratedFDeriv_linear_pos_le X p hj
  have hy := NormalComparison.InverseChartJet.norm_iteratedFDeriv_linear_pos_le Y p hj
  change ‖iteratedFDeriv ℝ j C p‖ ≤ _ ∧
    ‖iteratedFDeriv ℝ j X p‖ ≤ _ ∧ ‖iteratedFDeriv ℝ j Y p‖ ≤ _
  exact ⟨hc.trans (by linarith [norm_nonneg X, norm_nonneg Y]),
    hx.trans (by linarith [norm_nonneg C, norm_nonneg Y]),
    hy.trans (by linarith [norm_nonneg C, norm_nonneg X])⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
