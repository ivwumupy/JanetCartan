module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.ColoredApplication.TransportKernel

/-!
# Literal transport endpoint of the measured Hermitian kernel

Remove the carrier and phase extensions on their original plateaus. This
identifies the transport kernel with the literal zero polynomial and canonical
phase differential, keeping every cutoff and Fourier factor. The consumer is
the continuum-row identification in `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal Topology
namespace JanetCartan.Sampling.BackgroundModulation.ColoredApplication
open MeasuredAmplitude MeasuredAmplitude.ColoredApplication
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition FullPhaseCharts
open MeanNormalBound MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap ContinuumRow
open NormalComparison ColoredNormalComparison SeparatedSampling

variable {m N J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
      τ z x ξ‖ ≤ M)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular highPass η‖ ≤ B)


local notation "D₀" => retainedBackgroundModulationTransportKernelData (J := J)
  T Q F row col Φ Y r χ a hρ hP hcarrier hs M hM hb
  angular highPass ha hH hH₀ B hB hdB

/-- The actual transport kernel is the original canonical phase differential
and zero Hermitian polynomial on the same carrier buffer. The high-pass,
smooth radial band and Fourier scalar remain literal
(`app:ch_waves:eq:colored-normal-comparison`, `app:ch_background:eq:bg-T`). -/
theorem retainedBackgroundModulationTransportKernelData_kernel_eq_raw
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (j : Fin J) (z : Point)
    (hz : (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
      closedBall a.2 (ρ / 4))
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (D₀).kernel (j, z) η x =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (detectorMask angular highPass) j.val η) •
          (Complex.exp (Complex.I * (fderiv ℝ (phase T Q x)
            (T.reference.spatialPatch (WithLp.toLp 2 z)) η : ℂ)) •
            measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
              0 (WithLp.toLp 2 z) x (T.reference.spatialPatch (WithLp.toLp 2 z))) := by
  have hz' : WithLp.toLp 2 z ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hz
    exact closedBall_subset_closedBall (by linarith) hz.1
  have hamp := supportedBackgroundModulationPolynomial_eq_raw T Q F row col Φ Y r χ
    a hρ hχ hz 0 x 0 (by simp; positivity)
  simp only [add_zero] at hamp
  rw [BandKernelData.kernel, bandKernel,
    retainedBackgroundModulationTransportKernelData_amplitude]
  simp only [measuredBandAmplitude, zero_smul, add_zero]
  change (Complex.exp ((retainedTransportPhase T Q a hρ (((j, z), η), x) : ℂ) * Complex.I) *
      (Real.sqrt ‖η‖ : ℂ) * detectorMask angular highPass η) •
        (((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * radialBand (m + 1) j.val η : ℝ) : ℂ) •
          supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
            0 (WithLp.toLp 2 z) x
            (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z)) = _
  rw [extendedRetainedCarrier_eq T a.2.1 hρ hz', hamp]
  by_cases hx : χ x = 0
  · simp only [measuredBackgroundModulationPolynomial, hx, Complex.ofReal_zero,
      zero_smul, smul_zero]
  · have hbase : (x, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ phaseDomain T := by
      have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
        (retained_shift_mem_plateau T a (hχ hx) hz (d := 0) (by simp; positivity)))
      change (x, T.reference.spatialPatch (WithLp.toLp 2 z) + 0) ∈ phaseDomain T at hh
      simpa only [add_zero] using hh
    have heq : fderiv ℝ (extendedRetainedPhase T Q x)
        (T.reference.spatialPatch (WithLp.toLp 2 z)) =
        fderiv ℝ (phase T Q x) (T.reference.spatialPatch (WithLp.toLp 2 z)) := by
      apply Filter.EventuallyEq.fderiv_eq
      have hnhood : ∀ᶠ ξ in 𝓝 (T.reference.spatialPatch (WithLp.toLp 2 z)),
          (x, ξ) ∈ phaseDomain T :=
        (isOpen_ball.preimage (continuous_const.prodMk continuous_id)).mem_nhds hbase
      filter_upwards [hnhood] with ξ hξ
      exact extendedRetainedPhase_eq T Q hξ
    rw [retainedTransportPhase, extendedRetainedCarrier_eq T a.2.1 hρ hz', heq]
    simp only [weightedRadialBand, RCLike.real_smul_eq_coe_smul (K := ℂ),
      Complex.ofReal_mul, smul_smul]
    congr 1
    ac_rfl

end JanetCartan.Sampling.BackgroundModulation.ColoredApplication
