module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Literal

/-!
# The actual measured amplitude and its zero endpoint

Use the polynomial of the SAME full primary derivative to extend the measured
amplitude through zero. The literal inverse-frequency formula is only used
away from zero. The normalized homotopy retains the detector, the smooth wide
band, its half derivative, and the existing carrier/physical measurements.
The consumer is the actual normal-data matching for
`app:ch_waves:eq:colored-normal-comparison` and
`app:ch_waves:eq:sampling-operator-bounds`.

These are concrete coefficient identities. Smooth supported extensions and
uniform joint budgets must still be supplied on the initialized raw family.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RawKernel
open RawPrimary RawPrimary.AmplitudeGrades.Polynomial LeadingWave.FullModulation
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow FullPhaseCharts
open ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open MeanNormalBound.NormalizedFullPhase RawInputPartition

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
  (L : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin n))
  (χ : Euclidean n → ℝ)

/-- The actual measured derivative polynomial, including every correction
power. Its zero value is the leading principal matrix, not the totalized
inverse-frequency expression (`app:ch_waves:eq:WKB-amplitude-difference`). -/
def fullMeasuredDerivativePolynomial (τ : ℝ) (z : Euclidean 3)
    (x : Euclidean n) (ξ : Euclidean (n - 1)) : EuclideanSpace ℂ (Fin n) :=
  (χ x : ℂ) • L x
    (derivativePolynomial τ (fun w ↦ phaseGradient T Q w.1 w.2.2)
      (fullLeadingNormal T Q F row col Φ Y r)
      (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (fullLeadingReconstruction T Q F row col Φ Y r)
      (fullCorrectionReconstruction T Q F row col Φ Y r) (x, (z, ξ)))

/-- Exact equality with the measured derivative of `fullPrimaryAtom` at
nonzero frequency, from the published polynomial identity on the SAME fields
(`app:ch_waves:eq:individual-representation`). -/
theorem fullMeasuredDerivativePolynomial_eq {τ : ℝ} (hτ : τ ≠ 0)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    (hS : DifferentiableAt ℝ (fun y ↦ phase T Q y.1 y.2.2) w)
    (hν₀ : DifferentiableAt ℝ (fullLeadingNormal T Q F row col Φ Y r) w)
    (hν₁ : DifferentiableAt ℝ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) w)
    (hV₀ : DifferentiableAt ℝ (fullLeadingReconstruction T Q F row col Φ Y r) w)
    (hV₁ : DifferentiableAt ℝ (fullCorrectionReconstruction T Q F row col Φ Y r) w) :
    fullMeasuredDerivativePolynomial T Q F row col Φ Y r L χ τ w.2.1 w.1 w.2.2 =
      fullMeasuredDerivativeAmplitude T Q F row col Φ Y τ r L χ w.2.1 w.1 w.2.2 := by
  unfold fullMeasuredDerivativePolynomial
  rw [← fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r
    hτ hS hν₀ hν₁ hV₀ hV₁]
  rfl

/-- The actual zero endpoint is the retained leading principal matrix and
is independent of the radial/color label
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem fullMeasuredDerivativePolynomial_zero (z : Euclidean 3)
    (x : Euclidean n) (ξ : Euclidean (n - 1)) :
    fullMeasuredDerivativePolynomial T Q F row col Φ Y r L χ 0 z x ξ =
      (χ x : ℂ) • L x (fullLeadingPrincipalMatrix T Q F row col Φ Y r (x, (z, ξ))) := by
  rw [fullLeadingPrincipalMatrix_eq_tensor]
  simp [fullMeasuredDerivativePolynomial, derivativePolynomial, derivativeError]

/-- The normalized full amplitude in the retained canonical input chart.
The homotopy uses `τ = ε / 2^j`, the exact original band and unchanged
measurements; no sharp refinement indicator enters the symbol
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def fullMeasuredNormalAmplitude (d : Euclidean (n - 1) → ℂ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
    (ε : ℝ) (x u : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  let q := (adaptedSliceCoordinates T).equiv u
  let z := carrierParameters (v, q.1)
  ((ψ (carrierSamplingEquiv (q.1, v)) : ℂ) * (Real.sqrt ‖q.2‖ : ℂ) *
    weightedRadialBand d j ((2 : ℝ) ^ j • q.2)) •
      fullMeasuredDerivativePolynomial T Q F row col Φ Y r L χ (ε / (2 : ℝ) ^ j)
        z x (T.reference.spatialPatch z + ε • q.2)

/-- The normalized amplitude's zero endpoint keeps the original detector,
half derivative and smooth band, while all correction powers vanish
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem fullMeasuredNormalAmplitude_zero (d : Euclidean (n - 1) → ℂ)
    (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2) (x u : Euclidean n) :
    fullMeasuredNormalAmplitude T Q F row col Φ Y r L χ d ψ j v 0 x u =
      let q := (adaptedSliceCoordinates T).equiv u
      let z := carrierParameters (v, q.1)
      ((ψ (carrierSamplingEquiv (q.1, v)) : ℂ) * (Real.sqrt ‖q.2‖ : ℂ) *
        weightedRadialBand d j ((2 : ℝ) ^ j • q.2)) •
          ((χ x : ℂ) • L x (fullLeadingPrincipalMatrix T Q F row col Φ Y r
            (x, (z, T.reference.spatialPatch z)))) := by
  simp only [fullMeasuredNormalAmplitude, zero_div, zero_smul, add_zero,
    fullMeasuredDerivativePolynomial_zero]

section Normalization

variable {τ : ℝ} (hτ : τ ≠ 0) (d : Euclidean (n - 1) → ℂ)
  (ψ : SeparatedSampling.Point → ℝ) (j : ℕ) (v : Euclidean 2)
  (x : Euclidean n) (q : ℝ × Euclidean (n - 1))

local notation "z₀" => carrierParameters (v, Prod.fst q)
local notation "w₀" => (x, (z₀, T.reference.spatialPatch z₀ + (τ * (2 : ℝ) ^ j) • Prod.snd q))

include hτ in
/-- The homotopy at the actual parameter `ε = τ 2^j` equals the SAME
normalized measured raw amplitude. Only the local differentiability inputs
of the actual polynomial identity remain; no amplitude or kernel matching
equality is assumed. Together with `measuredBandAmplitude_normalization`,
this discharges the scalar/amplitude matching of the canonical mean endpoint
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullMeasuredNormalAmplitude_eq_normalized
    (hS : DifferentiableAt ℝ (fun y ↦ phase T Q y.1 y.2.2) w₀)
    (hν₀ : DifferentiableAt ℝ (fullLeadingNormal T Q F row col Φ Y r) w₀)
    (hν₁ : DifferentiableAt ℝ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) w₀)
    (hV₀ : DifferentiableAt ℝ (fullLeadingReconstruction T Q F row col Φ Y r) w₀)
    (hV₁ : DifferentiableAt ℝ (fullCorrectionReconstruction T Q F row col Φ Y r) w₀) :
    fullMeasuredNormalAmplitude T Q F row col Φ Y r L χ d ψ j v (τ * (2 : ℝ) ^ j)
      x ((adaptedSliceCoordinates T).equiv.symm q) =
      normalizedMeasuredAmplitude
        (fullMeasuredDerivativeAmplitude T Q F row col Φ Y τ r L χ)
        T.reference.spatialPatch (fun _ ↦ τ) d j z₀
        (ψ (carrierSamplingEquiv (q.1, v))) x q.2 := by
  simp only [fullMeasuredNormalAmplitude, ContinuousLinearEquiv.apply_symm_apply,
    mul_div_cancel_right₀ _ (show (2 : ℝ) ^ j ≠ 0 by positivity)]
  rw [fullMeasuredDerivativePolynomial_eq T Q F row col Φ Y r L χ hτ w₀
    hS hν₀ hν₁ hV₀ hV₁]
  rfl

end Normalization

end JanetCartan.Sampling.RawKernel
