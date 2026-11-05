module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CommonMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CarrierPullback
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.KernelWitnesses

/-!
# Literal matching after choosing the common physical cutoff

The measured Hermitian product is linear in its physical cutoff. Consequently
the same common output multiplication removes every local physical bump on
its plateau, while retaining the phase, transverse Jacobian, half derivative,
original angular detector and both quadratures. The finite-family sampling
assembly uses these identities before angular normal reassembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase RawKernel LeadingWave.FullModulation
open SamplingKernelBounds RawInputPartition ContinuumNormal

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (scalar : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)

/-- The SAME measured Hermitian polynomial, including the zero principal
endpoint, uses the common physical cutoff after output multiplication. This
is a literal coefficient identity, with no smoothness or operator premise
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem measuredBackgroundModulationPolynomial_common_cutoff
    (χ θ : Euclidean (m + 1) → ℝ) (hplateau : ∀ x, θ x ≠ 0 → χ x = 1)
    (τ : ℝ) (z : Euclidean 3) (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (θ x : ℂ) • measuredBackgroundModulationPolynomial T Q F row col Φ Y scalar χ τ z x η =
      measuredBackgroundModulationPolynomial T Q F row col Φ Y scalar θ τ z x η := by
  by_cases hx : θ x = 0
  · simp [measuredBackgroundModulationPolynomial, hx]
  · simp only [measuredBackgroundModulationPolynomial, hplateau x hx, Complex.ofReal_one, one_smul]

/-- The common cutoff commutes with the SAME retained joint extension; no
second working-ball or phase extension is selected
(`app:ch_waves:eq:individual-representation`). -/
theorem supportedBackgroundModulationPolynomial_common_cutoff
    (χ θ : Euclidean (m + 1) → ℝ) (hplateau : ∀ x, θ x ≠ 0 → χ x = 1)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) (τ : ℝ) (z : Euclidean 3) (x : Euclidean (m + 1))
    (η : Euclidean (m + 1 - 1)) :
    (θ x : ℂ) • supportedBackgroundModulationPolynomial T Q F row col Φ Y scalar χ
      a hρ τ z x η =
    supportedBackgroundModulationPolynomial T Q F row col Φ Y scalar θ a hρ τ z x η := by
  by_cases hx : θ x = 0
  · simp [supportedBackgroundModulationPolynomial, supportedMeasuredCrossDerivativePolynomial,
      measuredCrossDerivativePolynomial, hx]
  · simp only [supportedBackgroundModulationPolynomial, supportedMeasuredCrossDerivativePolynomial,
      measuredCrossDerivativePolynomial, hplateau x hx, Complex.ofReal_one, one_smul,
      smul_comm (θ x : ℂ)]

/-- The physical Fourier scalar, original radial band, carrier insertion and
inverse-frequency parameter are unchanged by the common physical cutoff
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem backgroundModulationBandAmplitude_common_cutoff {J p : ℕ}
    (χ θ : Euclidean (m + 1) → ℝ) (hplateau : ∀ x, θ x ≠ 0 → χ x = 1)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) (τ : (Fin 3 → Fin (p + 1)) → ℝ)
    (ζ : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point → Euclidean (m + 1 - 1))
    (q : ((Fin J × ((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)) ×
      Euclidean (m + 1 - 1)) × Euclidean (m + 1)) :
    (θ q.2 : ℂ) • measuredBandAmplitude
      (fun q ↦ supportedBackgroundModulationPolynomial T Q F row col Φ Y scalar χ
        a hρ (τ q.1) (WithLp.toLp 2 q.2)) ζ (fun q ↦ τ q.1) q =
    measuredBandAmplitude
      (fun q ↦ supportedBackgroundModulationPolynomial T Q F row col Φ Y scalar θ
        a hρ (τ q.1) (WithLp.toLp 2 q.2)) ζ (fun q ↦ τ q.1) q := by
  simp only [measuredBandAmplitude, smul_comm (θ q.2 : ℂ)]
  rw [supportedBackgroundModulationPolynomial_common_cutoff T Q F row col Φ Y scalar
    χ θ hplateau]

end JanetCartan.Sampling.BackgroundModulation
