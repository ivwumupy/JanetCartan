module

public import JanetCartan.Iteration.PhysicalForwardMean.NativeScalar
public import JanetCartan.Iteration.PhysicalSampling.OriginalKernel

/-!
# The original fixed-cutoff scalar kernel in the native moment convention

Every mask in this file is the ORIGINAL selector output. The real detector is
just the real coordinate of the literal original real-valued complex detector,
not a new cutoff. The full halfweight and Fourier normalization are retained.
Together with `nativeScalarOperator_ae_sampledMomentKernel`, the exact identity
below supplies the actual common-sample scalar tester for both mean14 and34.
No scalar operator norm, kernel equality, or mask regularity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalSampling PhysicalSamplingShells PhysicalMean Sampling Sampling.RawKernel
open SamplingKernelBounds Sampling.MeasuredAmplitude RawPrimary.MaskProfiles RawInputPartition ContinuumRow NormalComparison
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

/-- The real coordinate of the ORIGINAL angular/high-pass mask. It is not a
new mask or a cut-down source (`app:ch_background:defn:bg-row`). -/
def originalForwardDetector {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (η : Euclidean (n - 1)) : ℝ :=
  (detectorMask (originalConicDetector hηb hr)
    (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖) η).re

/-- The literal original complex detector is real-valued, so passing to its
real coordinate changes nothing in the original kernel. -/
theorem ofReal_originalForwardDetector {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (η : Euclidean (n - 1)) :
    (originalForwardDetector hηb hr η : ℂ) =
      detectorMask (originalConicDetector hηb hr)
        (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖) η := by
  simp [originalForwardDetector, detectorMask, originalConicDetector]

/-- Original detector regularity is proved from the selected masks, not
assumed when constructing the native scalar row. -/
theorem contDiff_originalForwardDetector {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) : ContDiff ℝ ∞ (originalForwardDetector hηb hr) := by
  exact Complex.reCLM.contDiff.comp (contDiff_detectorMask
    (originalConicDetector hηb hr) (fun ξ ↦ FixedCutoffs.highFrequency ‖ξ‖)
    (fun _ hη ↦ originalConicDetector_contDiffAt hηb hr hη)
    (contDiff_originalConicHighPass n) (fun _ hη ↦ FixedCutoffs.highFrequency_zero hη))

/-- Active original detector frequencies are strictly above one. This is the
actual high-pass source of the normalized-phase extension's `hhigh` premise. -/
theorem one_lt_norm_of_originalForwardDetector_ne_zero
    {n : ℕ} {ηb : Euclidean (n - 1)} {r : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) {η : Euclidean (n - 1)}
    (hη : originalForwardDetector hηb hr η ≠ 0) : 1 < ‖η‖ := by
  by_contra h
  apply hη
  simp [originalForwardDetector, detectorMask, FixedCutoffs.highFrequency_zero (not_lt.mp h)]

variable {m J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}

/-- Exact original scalar-band coordinate formula. All Fourier factors,
full raw retained phase, half-frequency factors and original masks agree
pointwise. This is the `hkernel` producer of the native scalar tester bridge,
not an assumed output identity (`app:ch_mean_pairs:eq:block-normal`). -/
theorem originalScalarKernelData_scalarBandKernel_eq
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall center.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {ηb : Euclidean (m + 1 - 1)} {r : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r)
    (τ : (Fin 3 → Fin (p + 1)) → ℝ) (hτ₀ : ∀ color, τ color ≠ 0)
    (j : Fin J) (q : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    scalarBandKernel (Nat.succ_le_succ (Nat.zero_le m))
      (originalScalarKernelData T Q χ center hρ hP hcarrier hηb hr τ hτ₀) (j,q) x η =
      (forwardScalarBandMask (m+1) (originalForwardDetector hηb hr) j.val η : ℂ) *
        oscillatoryFactor 1 (rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
          (extendedRetainedCarrier T center.2.1 hρ (WithLp.toLp 2 q.2)) (τ q.1) x η) *
            (χ x : ℂ) := by
  unfold scalarBandKernel originalScalarKernelData
  rw [retainedScalarKernelData_kernel]
  simp only [PiLp.smul_apply, scalarAuxiliaryAmplitude_component, smul_eq_mul,
    Complex.real_smul, weightedRadialBand, forwardScalarBandMask, Complex.ofReal_mul,
    ofReal_originalForwardDetector, oscillatoryFactor, one_mul]
  ring_nf

end JanetCartan.PhysicalForwardMean
