module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph

/-!
# Literal transport endpoints on the compatible carrier flow

Apply the actual scalar compatibility conclusion, retaining the same parent
minor, full and carrier flows, initial scalar, physical cutoff and tensor
measurement. The identities below feed the original-row identification in
`CanonicalChange` and the finite-current mean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling
open RawPrimary RawPrimary.AmplitudeGrades LeadingWave LeadingWave.FullModulation
open FullPhaseCharts
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive
open AmbientResponse RawKernel RetainedBackground

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (scalar : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y scalar
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y scalar w)
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2) ∈ V)

include hcompat hp

/-- The literal signed principal matrix on the full carrier graph is the
matrix of the SAME carrier normal. The premise is the compatibility output
of `exists_compatible_retained_sampling_primitives`; no normal identity is
assumed (`app:ch_waves:eq:arbitrary-b-amplitudes`, `app:ch_background:eq:bg-T`). -/
theorem fullLeadingPrincipalMatrix_eq_compatible_carrier :
    fullLeadingPrincipalMatrix T Q F row col Φ Y scalar (carrierGraph T p) =
      (principalMatrix (normalField T Q F row col φ y scalar p.1 p.2)
        (T.carrierGradient Q p.1 (parameter p.2))).map Complex.ofReal := by
  have hn := normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y scalar hcompat hp
  change (principalMatrix (fullNormal T Q F row col Φ Y scalar (carrierGraph T p))
    (phaseGradient T Q p.1 (T.reference.spatialPatch (parameter p.2)))).map Complex.ofReal = _
  rw [← hn, phaseGradient_on_carrier]

/-- Identify the measured polynomial's zero endpoint with the SAME carrier
normal, including the original physical cutoff and tensor contraction.
This is the exact amplitude identity for the canonical transport comparison
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem fullMeasuredDerivativePolynomial_zero_eq_compatible_carrier
    (measurement : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin n))
    (χ : Euclidean n → ℝ) :
    fullMeasuredDerivativePolynomial T Q F row col Φ Y scalar measurement χ 0
        (parameter p.2) p.1 (T.reference.spatialPatch (parameter p.2)) =
      (χ p.1 : ℂ) • measurement p.1
        ((principalMatrix (normalField T Q F row col φ y scalar p.1 p.2)
          (T.carrierGradient Q p.1 (parameter p.2))).map Complex.ofReal) := by
  rw [fullMeasuredDerivativePolynomial_zero]
  exact congrArg (fun A ↦ (χ p.1 : ℂ) • measurement p.1 A)
    (fullLeadingPrincipalMatrix_eq_compatible_carrier T Q F row col Φ Y φ y scalar hcompat hp)

/-- The actual eta-zero background is the original carrier tensor with the
literal physical cutoff. It is kept separate from angular mask reassembly
(`app:ch_waves:eq:background-quadrature`). -/
theorem localizedTransportBackground_eq_compatible_carrier (χ : Euclidean n → ℝ) :
    localizedTransportBackground T Q F row col Φ Y scalar χ (parameter p.2) p.1 =
      χ p.1 • (fun i j ↦ ‖normalField T Q F row col φ y scalar p.1 p.2‖ ^ 2 *
        T.carrierGradient Q p.1 (parameter p.2) i * T.carrierGradient Q p.1 (parameter p.2) j) := by
  have hn := normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y scalar hcompat hp
  change χ p.1 • (fun i j ↦
    ‖fullNormal T Q F row col Φ Y scalar (carrierGraph T p)‖ ^ 2 *
      phaseGradient T Q p.1 (T.reference.spatialPatch (parameter p.2)) i *
      phaseGradient T Q p.1 (T.reference.spatialPatch (parameter p.2)) j) = _
  rw [← hn, phaseGradient_on_carrier]

end JanetCartan.Sampling
