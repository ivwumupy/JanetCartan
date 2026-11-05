module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.RealizedIncidence.LocalData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.FullNormal

/-!
# Matching the common measurement to the same frozen carrier

The consumer is the finite Fourier assembly in `Spectral.CommonMeasurement`.
Only the measurement radius changes: the angular mask, inverse domain and
spectator ball retain the local patch data (`new:lem:scaling`,
`app:ch_background:prop:bg-frame`, `bg-full-complex-amplitude`).
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
    (hcell : 4 * d.a < 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρcell : 4 * ρ < 1 / 2)
    (hρa : 6 * ρ < d.a)

local notation "angular₀" => angularMask z₀ (NormedSpace.normalize ηb) d.ha
  (And.left (angularWidth_spec d.hηb d.hr))
local notation "e₀" => normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
  d.ha hcell angular₀ FixedCutoffs.highFrequency 0
local notation "eρ" => normalizedCarrierData T Q F d.row d.col Φ Y (fun _ ↦ 1)
  hρ hρcell angular₀ FixedCutoffs.highFrequency 0

/-- The literal smaller output chart retains all canonical functions and the
original angular mask (`app:ch_background:eq:bg-T`, `new:lem:scaling`). -/
theorem FrozenIncidencePatchData.commonMeasurement_chart :
    commonChartData e₀ (closedBall 0 (4 * ρ)) (FixedCutoffs.periodic hρ hρcell 1) = eρ := rfl

include hρa in
/-- The SAME carrier kernel, including its chart indicators, equals the
normalized carrier measured at the common radius (`app:ch_background:eq:bg-T`). -/
theorem FrozenIncidencePatchData.commonMeasurement_kernel (x : Torus n) (v : CarrierVariable n) :
    carrierKernel (restrictData e₀ (FixedCutoffs.periodic hρ hρcell 1)) x v =
      carrierKernel eρ x v :=
  carrierKernel_fixed_common_chart e₀ hρ d.ha hρcell hcell hρa rfl (fun _ _ ↦ rfl) rfl x v

include hρa in
/-- The restricted primitive coefficients are exactly those of the smaller
measurement, by the physical plateau product, with every other field fixed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem FrozenIncidencePatchData.commonMeasurement_coefficients :
    restrictCoefficients (coefficientsOfCarrier e₀ (FixedCutoffs.physical d.ha 1))
      (FixedCutoffs.physical hρ 1) = coefficientsOfCarrier eρ (FixedCutoffs.physical hρ 1) := by
  rw [coefficientsOfCarrier_normalizedCarrierData_zero,
    coefficientsOfCarrier_normalizedCarrierData_zero]
  have hm : (fun x : Euclidean n ↦
      FixedCutoffs.physical hρ 1 x * FixedCutoffs.physical d.ha 1 x) =
      FixedCutoffs.physical hρ 1 := by
    funext x
    exact physical_measurement_mul hρ d.ha (by linarith) x
  simp only [restrictCoefficients, hm]

omit Q F Φ Y hcell in
include hρa in
/-- The measured Euclidean zero extension of the cutoff output uses literally
the common physical cutoff. The half-open-cell indicator and Lebesgue measure
are retained (`app:ch_background:prop:bg-frame`, frozen Plancherel step). -/
theorem FrozenIncidencePatchData.commonMeasurement_measured_toEuclidean (w : OutputL2 n) :
    (fun x ↦ FixedCutoffs.physical d.ha 1 x •
      toEuclidean (𝕜 := ℝ) (cutoffMultiplier (FixedCutoffs.periodic hρ hρcell 1) w) x) =ᵐ[volume]
    (fun x ↦ FixedCutoffs.physical hρ 1 x • toEuclidean (𝕜 := ℝ) w x) := by
  let χ := FixedCutoffs.periodic (n := n) hρ hρcell 1
  have hm := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae (cutoffMultiplier_coeFn χ w))
  filter_upwards [toEuclidean_coe (𝕜 := ℝ) (cutoffMultiplier χ w),
    toEuclidean_coe (𝕜 := ℝ) w, hm] with x ht hw hm
  rw [ht, hw]
  by_cases hx : x ∈ halfOpenCell n
  · simp only [indicator_of_mem hx, periodicLift, Function.comp_apply]
    rw [hm hx]
    change FixedCutoffs.physical d.ha 1 x •
      (FixedCutoffs.physical hρ 1 (centeredTorusRepresentative (torusQuotient x)) •
        w (torusQuotient x)) = _
    rw [centeredTorusRepresentative_quotient hx, smul_smul, mul_comm,
      physical_measurement_mul hρ d.ha (by linarith)]
  · simp [hx]

end JanetCartan.ContinuumNormal.FrozenModel
