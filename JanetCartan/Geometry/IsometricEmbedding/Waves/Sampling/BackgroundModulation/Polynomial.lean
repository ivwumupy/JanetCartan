module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CompatibleTransportEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedBudgets

/-!
# The actual background-modulation polynomial

The canonical row uses the symmetric complex Hermitian product of the
background derivative with the modulated derivative. Both factors here are
the complete polynomial of the SAME retained raw field. In particular its
zero endpoint has the squared normal, as required by
`app:ch_background:setup:bg-wkb-input`; a fixed linear measurement of one
derivative has a different endpoint.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.BackgroundModulation
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive NullTransport

/-- The original complex symmetric Hermitian cross tensor, before taking
real quadratures. The first input is real-linear and conjugate-complex-linear;
the second retains complex linearity (`app:ch_background:setup:bg-wkb-input`). -/
def symmetricHermitianCross (N n : ℕ) :
    Matrix (Fin N) (Fin n) ℂ →L[ℝ]
      Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.mk₂ ℝ (fun A B ↦ matrixSymmetricPart (Aᴴ * B))
    (by
      intros
      ext i j
      simp [matrixSymmetricPart, Matrix.add_mul, mul_add]
      ring)
    (by
      intros
      ext i j
      simp [matrixSymmetricPart, Matrix.smul_mul, mul_add, mul_left_comm])
    (by
      intros
      ext i j
      simp [matrixSymmetricPart, Matrix.mul_add, mul_add]
      ring)
    (by
      intros
      ext i j
      simp [matrixSymmetricPart, Matrix.mul_smul, mul_add, mul_left_comm])).mkContinuous₂ 1
    (fun A B ↦ by
      change ‖matrixSymmetricPart (Aᴴ * B)‖ ≤ 1 * ‖A‖ * ‖B‖
      have hs : ‖matrixSymmetricPart (Aᴴ * B)‖ ≤ ‖Aᴴ * B‖ := by
        rw [matrixSymmetricPart, norm_smul]
        calc
          _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖Aᴴ * B‖ + ‖(Aᴴ * B)ᵀ‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
          _ = ‖Aᴴ * B‖ := by
            rw [Matrix.frobenius_norm_transpose]
            norm_num
            ring
      simpa only [one_mul, Matrix.frobenius_norm_conjTranspose] using
        hs.trans (Matrix.frobenius_norm_mul Aᴴ B))

/-- The same cross tensor has a dimension-independent Frobenius product
bound (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_symmetricHermitianCross_le (N n : ℕ) :
    ‖symmetricHermitianCross N n‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- At the original real principal matrix, the complex symmetric Hermitian
product is precisely its rank-one normal square
(`app:ch_background:setup:bg-wkb-input`). -/
theorem symmetricHermitianCross_principalMatrix {n N : ℕ}
    (ν : Euclidean N) (ξ : Euclidean n) :
    symmetricHermitianCross N n ((principalMatrix ν ξ).map Complex.ofReal)
        ((principalMatrix ν ξ).map Complex.ofReal) =
      (fun i j ↦ ((‖ν‖ ^ 2 * ξ i * ξ j : ℝ) : ℂ)) := by
  have hgram : ((principalMatrix ν ξ).map Complex.ofReal)ᴴ *
      ((principalMatrix ν ξ).map Complex.ofReal) =
        ((principalMatrix ν ξ)ᵀ * principalMatrix ν ξ).map Complex.ofReal := by
    ext i j
    simp [Matrix.mul_apply]
  change matrixSymmetricPart _ = _
  rw [hgram, principalMatrix_transpose_mul]
  ext i j
  simp only [matrixSymmetricPart, Matrix.smul_apply, Matrix.add_apply,
    Matrix.map_apply, Matrix.transpose_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (scalar : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The complete polynomial for two derivatives of the SAME retained atom,
with a common inverse frequency and independent covector slots. The physical
carrier substitution is made in `backgroundModulationPolynomial` below
(`app:ch_background:setup:bg-wkb-input`). -/
def crossDerivativePolynomial (τ : ℝ)
    (w₀ w₁ : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    Matrix (Fin n) (Fin n) ℂ :=
  let D := derivativePolynomial τ (fun w ↦ phaseGradient T Q w.1 w.2.2)
    (fullLeadingNormal T Q F row col Φ Y scalar)
    (fullCorrectionPrincipalNormal T Q F row col Φ Y scalar)
    (fullLeadingReconstruction T Q F row col Φ Y scalar)
    (fullCorrectionReconstruction T Q F row col Φ Y scalar)
  symmetricHermitianCross N n (D w₀) (D w₁)

/-- The original background covector is retained in the first derivative,
while only the second derivative is modulated. This is the literal amplitude
in `app:ch_background:setup:bg-wkb-input`. -/
def backgroundModulationPolynomial (τ : ℝ) (z : Euclidean 3)
    (x : Euclidean n) (ξ : Euclidean (n - 1)) : Matrix (Fin n) (Fin n) ℂ :=
  crossDerivativePolynomial T Q F row col Φ Y scalar τ
    (x, (z, T.reference.spatialPatch z)) (x, (z, ξ))

/-- The full zero endpoint is the product of the actual leading principal
matrices; every correction term vanishes at zero
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem crossDerivativePolynomial_zero
    (w₀ w₁ : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    crossDerivativePolynomial T Q F row col Φ Y scalar 0 w₀ w₁ =
      symmetricHermitianCross N n
        (fullLeadingPrincipalMatrix T Q F row col Φ Y scalar w₀)
        (fullLeadingPrincipalMatrix T Q F row col Φ Y scalar w₁) := by
  rw [fullLeadingPrincipalMatrix_eq_tensor, fullLeadingPrincipalMatrix_eq_tensor]
  simp [crossDerivativePolynomial, derivativePolynomial, derivativeError]

/-- On the original carrier the actual Hermitian zero amplitude has the
normal square of the SAME compatible flow. This is the continuum row's
amplitude, before its unchanged detector and physical cutoffs
(`app:ch_background:setup:bg-wkb-input`, `app:ch_background:eq:bg-T`). -/
theorem backgroundModulationPolynomial_zero_eq_compatible_carrier
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (NullTransport.FlowAmplitude.coordinates
        (NullTransport.ActualFlow.adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y scalar
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y scalar w)
    {p : Euclidean n × CarrierParameter}
    (hp : NullTransport.FlowAmplitude.coordinates
      (NullTransport.ActualFlow.adaptedCoordinates T.data.adapted) (p.1, parameter p.2) ∈ V) :
    backgroundModulationPolynomial T Q F row col Φ Y scalar 0 (parameter p.2) p.1
        (T.reference.spatialPatch (parameter p.2)) =
      fun i j ↦ ((‖normalField T Q F row col φ y scalar p.1 p.2‖ ^ 2 *
        T.carrierGradient Q p.1 (parameter p.2) i *
        T.carrierGradient Q p.1 (parameter p.2) j : ℝ) : ℂ) := by
  rw [backgroundModulationPolynomial, crossDerivativePolynomial_zero]
  change symmetricHermitianCross N n
    (fullLeadingPrincipalMatrix T Q F row col Φ Y scalar (carrierGraph T p))
    (fullLeadingPrincipalMatrix T Q F row col Φ Y scalar (carrierGraph T p)) = _
  rw [fullLeadingPrincipalMatrix_eq_compatible_carrier T Q F row col Φ Y φ y scalar hcompat hp]
  exact symmetricHermitianCross_principalMatrix _ _

end JanetCartan.Sampling.BackgroundModulation
