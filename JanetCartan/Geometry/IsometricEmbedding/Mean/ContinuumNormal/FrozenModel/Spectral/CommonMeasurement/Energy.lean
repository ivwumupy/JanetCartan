module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.CommonMeasurement.Matching

/-!
# Fourier energy after common measurement restriction

The old energy identity is a conclusion of `UnitRealization`, produced by
`exists_realized_frozen_incidence_patch`. Applying it to the cutoff output
proves the common-radius identity without another normal hypothesis or new
derivative bounds (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization CommonMeasurement
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU} {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)}
    (d : FrozenIncidencePatchData T z₀ ηb)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {ρ : ℝ} (hρ : 0 < ρ) (hρcell : 4 * ρ < 1 / 2)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) d.ha
  (And.left (angularWidth_spec d.hηb d.hr))
local notation "eρ" => normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
  hρ hρcell angular₀ FixedCutoffs.highFrequency 0
local notation "b₀" => canonicalFrozenCarrierSymbol T Q F d.row d.col Φ Y (fun _ ↦ 1)
  z₀ d.hηb d.hr d.ha

/-- The original real-quadrature energy at the cutoff output is precisely the
common measurement energy of the SAME symbol. The energy premise is the exact
conclusion of `UnitRealization` (`app:ch_background:prop:bg-frame`). -/
theorem FrozenIncidencePatchData.commonMeasurement_adjoint_energy (hρa : 6 * ρ < d.a)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (henergy : ∀ w : OutputL2 n, ‖(realQuadratureChannel V).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical d.ha 1 x • toEuclidean (𝕜 := ℝ) w x)))
    (w : OutputL2 n) :
    ‖(realQuadratureChannel (restrictCarrier (FixedCutoffs.periodic hρ hρcell 1) V)).adjoint w‖ ^ 2 =
      euclideanFrozenEnergy b₀ (fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hρ 1 x • toEuclidean (𝕜 := ℝ) w x)) := by
  change ‖(carrierChannel (restrictCarrier (FixedCutoffs.periodic hρ hρcell 1) V)).adjoint w‖ ^ 2 = _
  rw [carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint]
  change ‖(realQuadratureChannel V).adjoint
    (cutoffMultiplier (FixedCutoffs.periodic hρ hρcell 1) w)‖ ^ 2 = _
  rw [henergy]
  apply euclideanFrozenEnergy_congr_ae
  filter_upwards [d.commonMeasurement_measured_toEuclidean hρ hρcell hρa w] with x hx
  exact congrArg euclideanComplexInclusion hx

/-- The common-radius full reflected amplitude separates with the original
canonical symbol and physical conversion `k = 2πξ`. In particular neither
reflection nor the quadrature factor four is changed (`new:lem:scaling`,
`app:ch_background:eq:bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem FrozenIncidencePatchData.commonMeasurement_amplitude_symbol
    {c C : ℝ} (hP : P.IsValid c C) (hgeom : d.Geometry Q)
    (ξ x y : Euclidean n) (i j : Fin n) :
    fullReflectedMatrixAmplitude (coefficientsOfCarrier eρ (FixedCutoffs.physical hρ 1))
      (transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0))
      (frozenSymbolInverse T Q z₀ ηb d.r (6 * d.a))
      (frozenSymbolDomain T Q z₀ ηb d.r (6 * d.a))
      (closedBall (spectatorCenter z₀) (d.a / 2)) ξ (pairedPosition x y) i j =
        (FixedCutoffs.physical hρ 1 x : ℂ) * (FixedCutoffs.physical hρ 1 y : ℂ) *
          (b₀ ((2 * Real.pi) • ξ) i j : ℂ) := by
  have har : 6 * d.a ≤ 3 * d.r := by linarith [d.har, d.hr]
  have hh := fullReflectedMatrixAmplitude_normalizedCarrierData_zero T Q F d.row d.col Φ Y
    (fun _ ↦ 1) angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
    hP d.hηb d.hr har d.hcarrier hgeom.2.2.1 hgeom.2.2.2 hρ hρcell
    (closedBall (spectatorCenter z₀) (d.a / 2)) x y ξ
  simpa only [canonicalFrozenCarrierSymbol, Pi.smul_apply, Complex.real_smul,
    Complex.ofReal_mul] using congrArg (fun m ↦ m i j) hh

end JanetCartan.ContinuumNormal.FrozenModel
