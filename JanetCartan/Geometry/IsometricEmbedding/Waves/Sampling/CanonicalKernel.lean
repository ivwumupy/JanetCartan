module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Construction

/-!
# Sampling the actual canonical differentiated atom

The measured vector amplitude below is a selected complex-linear tensor
contraction of the SAME canonical derivative amplitude used by
`RawPrimary.fullPrimaryWave`. The pointwise kernel identity is proved from the
canonical reconstruction, including both terms of the primary wave. It does
not assume an operator identity or discard either quadrature.

Regularity and uniform coefficient budgets on one common family still have
their actual producers in `RawPrimary`; the identities here are the algebraic
connection required by `app:ch_waves:eq:sampling-prefix-normal`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RawKernel
open RawPrimary LeadingWave.FullModulation SamplingKernelBounds RawInputPartition
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  (F : Euclidean n → Euclidean N) (row col : Fin n)
  (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
    Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
  (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
  (L : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin n))
  (χ : Euclidean n → ℝ)

/-- The concrete coefficient supplied to `bandKernelData`, before adding the
Fourier scalar and smooth radial band. `L` is the selected tensor contraction
in the sampling theorem and `χ` its physical measurement
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def fullMeasuredDerivativeAmplitude (z : Euclidean 3) (x : Euclidean n)
    (ξ : Euclidean (n - 1)) : EuclideanSpace ℂ (Fin n) :=
  (χ x : ℂ) • L x (canonicalDerivativeAmplitude F τ (fun p ↦ phase T Q p.1 p.2)
    (fun p ↦ euclideanComplexInclusion
      (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
    (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2))) (x, ξ))

/-- The measured smooth-band kernel is the actual demodulated derivative of
`fullPrimaryAtom`, hence of the integrand of `fullPrimaryWave`. The only
hypotheses are the local differentiability inputs of canonical reconstruction;
their actual producer is the common corrected family. The contraction is
complex-linear and retains both quadratures
(`app:ch_waves:eq:individual-representation`,
`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullMeasuredDerivativeAmplitude_kernel
    (hτ : τ ≠ 0) (d : Euclidean (n - 1) → ℂ) (j : Fin J) (z : Euclidean 3)
    (η : Euclidean (n - 1)) {V : Set (Euclidean n)} (hV : IsOpen V)
    {x : Euclidean n} (hx : x ∈ V)
    (hS : DifferentiableOn ℝ
      (fun y ↦ phase T Q y (T.reference.spatialPatch z + τ • η)) V)
    (hb₀ : DifferentiableOn ℝ
      (fun y ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r
        (y, (z, T.reference.spatialPatch z + τ • η)))) V)
    (hb₁ : DifferentiableOn ℝ
      (fun y ↦ fullCorrectionCovector T Q F row col Φ Y r
        (y, (z, T.reference.spatialPatch z + τ • η))) V)
    (hA : DifferentiableAt ℝ
      (fun y ↦ canonicalDisplacementAmplitude F τ (fun p ↦ phase T Q p.1 p.2)
        (fun p ↦ euclideanComplexInclusion
          (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
        (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2)))
        (y, T.reference.spatialPatch z + τ • η)) x) :
    bandKernel
      (fun η x ↦ rawPrimaryPhaseDifference (phase T Q) (T.reference.spatialPatch z) τ x η)
      d
      (fun η x ↦ measuredBandAmplitude
        (fullMeasuredDerivativeAmplitude T Q F row col Φ Y τ r L χ)
        T.reference.spatialPatch (fun _ ↦ τ) (((j, z), η), x)) η x =
    (((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) •
      (((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η) •
        ((χ x : ℂ) • L x
          (Complex.exp (-Complex.I * (phase T Q x (T.reference.spatialPatch z) / τ : ℝ)) •
            (fun i k ↦ partialDeriv
              (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r z
                (y, T.reference.spatialPatch z + τ • η)) x k i)))) := by
  have h := canonicalAtomDerivative_demodulated F hτ hV hx
    (T.reference.spatialPatch z) η hS hb₀ hb₁ hA
  change bandKernel _ d _ η x =
    (((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) •
      (((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η) •
        ((χ x : ℂ) • L x
          (Complex.exp (-Complex.I * (phase T Q x (T.reference.spatialPatch z) / τ : ℝ)) •
            canonicalAtomDerivative F τ (fun p ↦ phase T Q p.1 p.2)
              (fun p ↦ euclideanComplexInclusion
                (fullLeadingCovector T Q F row col Φ Y r (p.1, (z, p.2))))
              (fun p ↦ fullCorrectionCovector T Q F row col Φ Y r (p.1, (z, p.2)))
              (x, T.reference.spatialPatch z + τ • η))))
  rw [h, map_smul]
  simp only [bandKernel, measuredBandAmplitude, fullMeasuredDerivativeAmplitude,
    weightedRadialBand, Complex.ofReal_mul, smul_smul]
  congr 1
  rw [mul_comm (rawPrimaryPhaseDifference _ _ _ _ _ : ℂ) Complex.I]
  ring

end JanetCartan.Sampling.RawKernel
