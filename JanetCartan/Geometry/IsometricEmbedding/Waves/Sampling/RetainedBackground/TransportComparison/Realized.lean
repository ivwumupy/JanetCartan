module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CarrierBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.TransportComparison.L2

/-!
# The original localized transported tensor

Name the exact zero endpoint of the retained polynomial, without introducing
any prepared scalar. Consumer: the L2 comparison adjacent to
`app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open AmbientResponse ResponseTransfer

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The original transported rank-one tensor, with the same physical cutoff,
carrier covector and scalar amplitude as the actual zero-input background
(the comparison adjacent to `app:ch_waves:eq:background-quadrature`). -/
def localizedTransportBackground (χ : Euclidean n → ℝ)
    (z : Euclidean 3) (x : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  χ x • (fun i j ↦
    ‖principalNormal (canonicalNormalCompletion F x)
      (phaseGradient T Q x (T.reference.spatialPatch z))
      (fullLeadingCovector T Q F row col Φ Y r
        (x, (z, T.reference.spatialPatch z)))‖ ^ 2 *
      phaseGradient T Q x (T.reference.spatialPatch z) i *
      phaseGradient T Q x (T.reference.spatialPatch z) j)

/-- The transported tensor is exactly the polynomial endpoint, including the
original cutoff and all original profiles (`app:ch_waves:eq:background-quadrature`). -/
theorem localizedTransportBackground_eq_polynomial_zero (χ : Euclidean n → ℝ)
    (z : Euclidean 3) (x : Euclidean n) :
    localizedTransportBackground T Q F row col Φ Y r χ z x =
      χ x • backgroundPolynomial T Q F row col Φ Y r 0
        (x, (z, T.reference.spatialPatch z)) := by
  rw [backgroundPolynomial_zero]
  rfl

end JanetCartan.Sampling.RetainedBackground
