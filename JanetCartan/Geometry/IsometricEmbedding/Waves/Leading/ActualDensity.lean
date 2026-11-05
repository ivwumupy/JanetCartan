module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.PrincipalNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.PositiveBound

/-!
# Initial-density dependence of the actual transported principal tensor

The amplitude is the literal characteristic formula, with the same flow,
footpoint and null column. Squaring that formula discharges the density
factorization in `app:ch_waves:thm:leading`; no factorization is assumed.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open AmbientResponse

/-- The principal Hermitian tensor of the actual transport solution is linear
in its prescribed initial density. The coefficient uses initial scalar one,
so is independent of `r` (`app:ch_waves:thm:leading`). -/
theorem carrierScalarAmplitude_principal_tensor_density {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (w : Euclidean n × Euclidean 3) :
    let ξ := T.carrierGradient Q w.1 w.2
    let k := carrierNullvector T Q col w
    let α := carrierScalarAmplitude T Q F row col Φ Y r w
    hermitianTensor ((principalMatrix
      (principalNormal (canonicalNormalCompletion F w.1) ξ (α • k)) ξ).map Complex.ofReal) =
      (carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) w ^ 2 *
        r (Y (coordinates (adaptedCoordinates T.data.adapted) w)) ^ 2) •
      hermitianTensor ((principalMatrix
        (principalNormal (canonicalNormalCompletion F w.1) ξ k) ξ).map Complex.ofReal) := by
  dsimp only
  rw [hermitianTensor_ofReal, hermitianTensor_ofReal, principalNormal_density_scaling,
    carrierScalarAmplitude_sq]

end JanetCartan.LeadingWave
