module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude

/-!
# Literal scalar transport for the canonical adjoint

Extract the original initial scalar, flow factor, and geometric normal from
`CanonicalCarrier.data`, as required by `Assembly.ScalarTransport`. The exact
factorization below uses the ODE footpoint. Identifying that footpoint with
`CanonicalCarrier.transportPosition = d_ζ S` on the complete supported chart
is a separate geometric obligation; it is not an assumption hidden in these
definitions or a consequence of the factorization.

Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
and `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport LeadingWave AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The prescribed scalar in the literal `(z,y)` order used by the raw
adjoint endpoint (`app:ch_background:prop:bg-adjoint`). -/
def initialScalar (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : CarrierVariable n) : ℝ := initial (p.2, CanonicalCarrier.parameter p.1)

/-- The actual constructed inverse-flow evaluation. Both the initial spatial
point and the carrier label are retained (`app:ch_waves:thm:leading`). -/
def odeInitialPoint
    (Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : CarrierParameter × Euclidean n) : Euclidean (n - 1) × Euclidean 3 :=
  Y (FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)
    (p.2, CanonicalCarrier.parameter p.1))

/-- The literal exponential transport factor, obtained by setting the initial
scalar to one (`app:ch_background:prop:bg-adjoint`). -/
def flowFactor (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (p : CarrierParameter × Euclidean n) : ℝ :=
  carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)
    (p.2, CanonicalCarrier.parameter p.1)

/-- Canonical normal with the scalar transport removed. This is the `ν`
input of `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:eq:bg-T`). -/
def geometricNormal (F : Euclidean n → Euclidean N) (col : Fin n)
    (p : CarrierParameter × Euclidean n) : Euclidean N :=
  principalNormal (canonicalNormalCompletion F p.2)
    (T.carrierGradient Q p.2 (CanonicalCarrier.parameter p.1))
    (carrierNullvector T Q col (p.2, CanonicalCarrier.parameter p.1))

/-- The scalar formula is derived from the actual exponential integral, with
the prescribed initial function evaluated at the actual inverse flow. No
phase-footpoint identification is used (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierScalarAmplitude_eq_initial_flow
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : CarrierParameter × Euclidean n) :
    carrierScalarAmplitude T Q F row col Φ Y initial
        (p.2, CanonicalCarrier.parameter p.1) =
      initial (odeInitialPoint T Y p) * flowFactor T Q F row col Φ Y p := by
  simp only [carrierScalarAmplitude, transportFromFootpoint, characteristicTransport,
    scalarTransport, odeInitialPoint, flowFactor, mul_one]
  ring

/-- Exact scalar/flow/geometric-normal factorization for the SAME canonical
carrier, before replacing the ODE footpoint by phase coordinates
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-adjoint`). -/
theorem normalField_eq_initial_flow
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (x : Euclidean n) (z : CarrierParameter) :
    CanonicalCarrier.normalField T Q F row col Φ Y initial x z =
      (initial (odeInitialPoint T Y (z,x)) * flowFactor T Q F row col Φ Y (z,x)) •
        geometricNormal T Q F col (z,x) := by
  rw [CanonicalCarrier.normalField_eq_scalar_smul]
  rw [carrierScalarAmplitude_eq_initial_flow T Q F row col Φ Y initial (z,x)]
  rfl

end JanetCartan.ContinuumAdjoint.Canonical
