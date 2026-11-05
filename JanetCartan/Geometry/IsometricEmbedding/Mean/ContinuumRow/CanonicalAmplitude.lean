module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.PositiveBound

/-!
# The literal normal amplitude and initial density

These identities connect the actual scalar formula to the continuum carrier
and to the primitive coefficients of its full normal. They retain the ODE
footpoint in the initial density, separately from the Hamilton covector
derivative used in the oscillatory phase (`app:ch_background:eq:bg-T`).
No amplitude estimate or carrier-operator bound is assumed here.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport LeadingWave AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The actual normal is the scalar transport times the fixed canonical
null-column normal (`app:ch_background:defn:bg-carriers`). -/
theorem normalField_eq_scalar_smul (x : Euclidean n) (z : CarrierParameter) :
    normalField T Q F row col Φ Y initial x z =
      carrierScalarAmplitude T Q F row col Φ Y initial (x, parameter z) •
        principalNormal (canonicalNormalCompletion F x)
          (T.carrierGradient Q x (parameter z)) (carrierNullvector T Q col (x, parameter z)) :=
  principalNormal_smul _ _ _ _

/-- The squared normal amplitude retains precisely the squared initial datum
evaluated at the SAME constructed footpoint. This is the density dependence
needed by the positive-background consumer (`app:ch_background:eq:bg-T`,
`app:ch_waves:thm:leading`). -/
theorem normalField_norm_sq_eq_density (x : Euclidean n) (z : CarrierParameter) :
    ‖normalField T Q F row col Φ Y initial x z‖ ^ 2 =
      initial (Y (FlowAmplitude.coordinates
        (ActualFlow.adaptedCoordinates T.data.adapted) (x, parameter z))) ^ 2 *
      ‖normalField T Q F row col Φ Y (fun _ ↦ 1) x z‖ ^ 2 := by
  rw [normalField_eq_scalar_smul, normalField_eq_scalar_smul]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [carrierScalarAmplitude_sq]
  ring

variable {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

/-- The physical measurement cutoff in the full normal agrees literally
with the torus cutoff used by the image channel (`app:ch_background:defn:bg-row`). -/
theorem data_measurement (x : Torus n) :
    FixedCutoffs.physical hr 1
        ((data T Q F row col Φ Y initial hr hcell angular high).chartPoint x) =
      (data T Q F row col Φ Y initial hr hcell angular high).measurementCutoff x := rfl

/-- Primitive coefficients of the SAME literal carrier. The reduced entry is
the existing actual detector, so the symbol construction and incidence frame
use identical stress contractions (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem coefficientsOfCarrier_data :
    TransportKernel.coefficientsOfCarrier
      (data T Q F row col Φ Y initial hr hcell angular high) (FixedCutoffs.physical hr 1) =
    ({ measurement := FixedCutoffs.physical hr 1
       angular := fun p ↦ angular p.1 p.2
       high := high
       normal := fun p ↦ normalField T Q F row col Φ Y initial p.1 p.2
       reduced := fun p ↦ ActualCarriers.quadratic (Q.1 p.1)
         (T.carrierGradient Q p.1 (parameter p.2)) } :
       ContinuumNormalReduction.TransportSymbol.Coefficients n N) := by
  unfold TransportKernel.coefficientsOfCarrier
  simp only [reducedCovector_data]
  rfl

end JanetCartan.ContinuumRow.CanonicalCarrier
