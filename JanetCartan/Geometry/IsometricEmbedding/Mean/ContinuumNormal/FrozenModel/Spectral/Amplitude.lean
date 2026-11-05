module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Inverse

/-!
# Exact measurement factorization of the frozen full amplitude

The Fourier consumer in the frozen step of `app:ch_background:prop:bg-frame`
needs the actual two-position full reflected matrix, not only its value at
the origin. The identities below retain the original high and angular masks,
the same spectator set and Lebesgue measure, both reflections, the factor
four, and the physical conversion `k = 2πξ`. Integrability is a separate
obligation; these identities do not infer it from the totalized integral.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel ConicChart

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (c : TransportSliceCoordinates n) (measurement : Euclidean n → ℝ)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (hηb : ηb ≠ 0) (hr : 0 < r) (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))

local notation "a₀" => uncutFrozenCoefficients T Q F row col Φ Y initial angular high
local notation "J₀" => transportAbsoluteJacobian c (normalizedTransportPosition T Q 0)
local notation "u₀" => frozenSymbolInverse T Q z₀ ηb r a
local notation "Ω₀" => frozenSymbolDomain T Q z₀ ηb r a

include hP hr har hcarrier

/-- Before integration the literal frozen density has exactly the two
measurement factors. No support or Jacobian identity is postulated
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenInputDensity_measurement {p : InputVariables n}
    (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    inputDensity {a₀ with measurement := measurement} J₀ p =
      (measurement p.1.1 * measurement p.1.2) • inputDensity a₀ J₀ (originInput p) := by
  have hj := frozenJacobian_position T Q hP hr har hcarrier c hp
  ext i j
  simp only [inputDensity, inputWeight, uncutFrozenCoefficients, originInput,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [hj]
  simp only [originInput]
  ring

variable
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
include hηb hInv htrans

/-- The chart's zero extension respects measurement factorization, including
all points outside the actual inverse domain
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenExtendedDensity_measurement (p : Variables n × Euclidean 2) :
    extendedDensity {a₀ with measurement := measurement} J₀ u₀ Ω₀ p =
      (measurement p.1.1 * measurement p.1.2.1) •
        extendedDensity a₀ J₀ u₀ Ω₀ (originOutput p) := by
  by_cases hp : p ∈ Ω₀
  · have ho : originOutput p ∈ Ω₀ := hp
    rw [extendedDensity, indicator_of_mem hp, extendedDensity, indicator_of_mem ho]
    exact frozenInputDensity_measurement T Q F row col Φ Y initial angular high c measurement
      hP hr har hcarrier (frozenSymbolInverse_maps T Q hηb hr hInv htrans hp)
  · have ho : originOutput p ∉ Ω₀ := hp
    simp only [extendedDensity, indicator_of_notMem hp, indicator_of_notMem ho, smul_zero]

/-- The original Lebesgue spectator integral has the same two measurement
factors, with no integration-measure renormalization
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenAmplitude_measurement (S : Set (Euclidean 2)) (x y k : Euclidean n) :
    amplitude {a₀ with measurement := measurement} J₀ u₀ Ω₀ S (x, y, k) =
      (measurement x * measurement y) • amplitude a₀ J₀ u₀ Ω₀ S (0, 0, k) := by
  simp only [amplitude]
  simp_rw [frozenExtendedDensity_measurement T Q F row col Φ Y initial angular high c measurement
    hP hηb hr har hcarrier hInv htrans]
  exact integral_smul _ _

/-- The full reflected matrix is exactly the measured frozen carrier symbol.
The original reflection normalization and physical `2π` conversion are
unchanged (`app:ch_background:eq:bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_frozen_measurement
    (S : Set (Euclidean 2)) (x y ξ : Euclidean n) :
    fullReflectedMatrixAmplitude {a₀ with measurement := measurement} J₀ u₀ Ω₀ S ξ
      (AmplitudeBound.pairedPosition x y) =
      (measurement x * measurement y) •
        (fun i j ↦ (frozenCarrierSymbol T Q F row col Φ Y initial angular high c u₀ Ω₀ S
          ((2 * Real.pi) • ξ) i j : ℂ)) := by
  ext i j
  rw [fullReflectedMatrixAmplitude_pairedPosition]
  simp only [reflectedSymbolAmplitude, frozenCarrierSymbol]
  rw [frozenAmplitude_measurement T Q F row col Φ Y initial angular high c measurement
    hP hηb hr har hcarrier hInv htrans,
    frozenAmplitude_measurement T Q F row col Φ Y initial angular high c measurement
      hP hηb hr har hcarrier hInv htrans]
  simp only [Matrix.smul_apply, Matrix.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add]
  push_cast
  ring

/-- Fourier-consumer matching for the measured coefficients of the literal
normalized carrier. Both physical measurement factors and all inverse-domain
restrictions have been discharged (`new:lem:scaling`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem fullReflectedMatrixAmplitude_normalizedCarrierData_zero
    {ρ : ℝ} (hρ : 0 < ρ) (hcell : 4 * ρ < 1 / 2)
    (S : Set (Euclidean 2)) (x y ξ : Euclidean n) :
    fullReflectedMatrixAmplitude
      (TransportKernel.coefficientsOfCarrier
        (normalizedCarrierData T Q F row col Φ Y initial hρ hcell angular high 0)
        (FixedCutoffs.physical hρ 1)) J₀ u₀ Ω₀ S ξ
      (AmplitudeBound.pairedPosition x y) =
      (FixedCutoffs.physical hρ 1 x * FixedCutoffs.physical hρ 1 y) •
        (fun i j ↦ (frozenCarrierSymbol T Q F row col Φ Y initial angular high c u₀ Ω₀ S
          ((2 * Real.pi) • ξ) i j : ℂ)) := by
  rw [coefficientsOfCarrier_normalizedCarrierData_zero]
  exact fullReflectedMatrixAmplitude_frozen_measurement T Q F row col Φ Y initial angular high c
    (FixedCutoffs.physical hρ 1) hP hηb hr har hcarrier hInv htrans S x y ξ

end JanetCartan.ContinuumNormal.FrozenModel
