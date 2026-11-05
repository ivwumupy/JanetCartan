module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.Density

/-!
# Density factors for the existing canonical carrier

The elementary density identity is instantiated with the actual scalar
transport and its ODE footpoint, using `normalField_norm_sq_eq_density`.
The ODE footpoint is distinct from the Hamilton transport map defining the
oscillatory phase. Consumer: the small-density comparison in
`app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumNormalReduction.TransportSymbol
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

/-- The density of the SAME canonical carrier has the initial scalar squared
at both actual ODE footpoints. All remaining factors are those of the carrier
with initial scalar one, with no estimate or equality of normal operators
among the hypotheses. Source: `app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem canonical_inputDensity_initial
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n) :
    let coeff := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    let foot := fun x ↦ Y (FlowAmplitude.coordinates
      (ActualFlow.adaptedCoordinates T.data.adapted) (x, parameter p.2.1))
    inputDensity (coeff initial) J p =
      (initial (foot p.1.1) ^ 2 * initial (foot p.1.2) ^ 2) •
        inputDensity (coeff (fun _ ↦ 1)) J p := by
  dsimp only
  rw [coefficientsOfCarrier_data, coefficientsOfCarrier_data]
  ext i j
  simp only [inputDensity, inputWeight, Matrix.smul_apply, smul_eq_mul]
  rw [normalField_norm_sq_eq_density T Q F row col Φ Y initial,
    normalField_norm_sq_eq_density T Q F row col Φ Y initial]
  ring

/-- The v2 density perturbation occurs twice in the literal canonical normal
density, at the two constructed footpoints. This specializes the actual
initial-value formula, rather than assuming a factorization of the amplitude.
Source: `app:ch_background:prop:bg-frame`. -/
theorem canonical_inputDensity_sqrtDensity
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (J : InputVariables n → ℝ) (p : InputVariables n)
    (hv : ∀ x ∈ ({p.1.1, p.1.2} : Set (Euclidean n)),
      0 ≤ 1 + v (Y (FlowAmplitude.coordinates
        (ActualFlow.adaptedCoordinates T.data.adapted) (x, parameter p.2.1)))) :
    let coeff := fun initial ↦ TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1)
    let foot := fun x ↦ Y (FlowAmplitude.coordinates
      (ActualFlow.adaptedCoordinates T.data.adapted) (x, parameter p.2.1))
    inputDensity (coeff (fun q ↦ Real.sqrt (1 + v q))) J p =
      ((1 + v (foot p.1.1)) * (1 + v (foot p.1.2))) •
        inputDensity (coeff (fun _ ↦ 1)) J p := by
  dsimp only
  rw [canonical_inputDensity_initial T Q F row col Φ Y hr hcell angular high,
    Real.sq_sqrt (hv _ (by simp)), Real.sq_sqrt (hv _ (by simp))]

end JanetCartan.ContinuumNormal.CarrierVariation
