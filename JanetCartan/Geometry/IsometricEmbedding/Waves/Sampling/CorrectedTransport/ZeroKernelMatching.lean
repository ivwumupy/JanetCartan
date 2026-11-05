module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.ZeroKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Support

/-!
# Exact matching of the leading kernel and corrected zero normal

The original phase extension agrees on the nonzero leading coefficient.
The same Fourier normalization identifies the leading kernel amplitude with
the corrected transport path at zero, including the high-pass transition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition SamplingKernelBounds
open CanonicalAtomRealization MeasuredAmplitude.ColoredApplication SeparatedSampling
open MeanNormalBound.CanonicalGap NormalComparison RawPrimary.SliceBounds FullPhaseCharts.ActualComparison
open CurrentMean NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
    Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)


variable {J : ℕ}
    (hκc : HasCompactSupport κ)
    (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
    (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (hd : Continuous (detectorMask angular highPass))
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖detectorMask angular highPass η‖ ≤ Md)

local notation "D₀" => leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
  hκc hA₀ hC hP hcarrier (detectorMask angular highPass) hd Md hMd hdb J

/-- The leading kernel phase is the literal zero phase of the corrected
homotopy wherever its amplitude is nonzero. The original physical and carrier
buffers suffice (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem leadingCrossTransportKernelData_phase_on_zero_support
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (haz : a.2.1 = z₀) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (ψ : Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (τ : ℝ) (j : Fin J) (v : Euclidean 2) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (x : Euclidean (m + 1))
    (hn : correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
      angular highPass ψ j.val v 0 x (fullInputCoordinates m (s, θ)) ≠ 0) :
    (D₀).phase (((j, carrierSamplingEquiv (s, v)), (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * normalizedFullPhase T Q v 0 x
        (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) := by
  obtain ⟨hx, hz, _, _⟩ := correctedTransportNormalAmplitude_nonzero
    T Q F row col Φ Y χ B r κ C z₀ hρ τ angular highPass ψ j.val v 0 x s θ hn
  have hzg := hψgraph s v hz
  have hzc : carrierParameters (v, s) ∈ closedBall z₀ ρ := by
    rw [← closedBall_prod_same] at hzg
    rw [← haz]
    exact closedBall_subset_closedBall (by linarith) hzg.1
  have hbase : (x, T.reference.spatialPatch (carrierParameters (v, s))) ∈ phaseDomain T := by
    have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
      (retained_shift_mem_plateau T a (hκ hx) hzg (d := 0) (by simp; positivity)))
    change (x, T.reference.spatialPatch (carrierParameters (v, s)) + 0) ∈ phaseDomain T at hh
    simpa only [add_zero] using hh
  have heq : fderiv ℝ (extendedRetainedPhase T Q x)
      (T.reference.spatialPatch (carrierParameters (v, s))) =
      fderiv ℝ (phase T Q x) (T.reference.spatialPatch (carrierParameters (v, s))) := by
    apply Filter.EventuallyEq.fderiv_eq
    have hnhood : ∀ᶠ ξ in 𝓝 (T.reference.spatialPatch (carrierParameters (v, s))),
        (x, ξ) ∈ phaseDomain T :=
      (isOpen_ball.preimage (continuous_const.prodMk continuous_id)).mem_nhds hbase
    filter_upwards [hnhood] with ξ hξ
    exact extendedRetainedPhase_eq T Q hξ
  change retainedTransportPhase T Q (0, z₀, T.reference.spatialPatch z₀) hρ
    (((j, carrierSamplingEquiv (s, v)), (2 : ℝ) ^ j.val • θ), x) = _
  rw [retainedTransportPhase, ← carrierParameters_eq_sampling,
    extendedRetainedCarrier_eq T z₀ hρ hzc, heq,
    normalizedFullPhase_canonicalInputCoordinates_zero, map_smul]
  rfl

/-- The zero homotopy amplitude and the leading transport kernel have the
same Fourier scalar, Jacobian, auxiliary weight and full detector. Only the
original carrier-extension plateau is used
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem leadingCrossTransportKernelData_amplitude_eq_zeroHomotopy
    (ψ : Point → ℝ)
    (hψ : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      carrierParameters (v, s) ∈ closedBall z₀ ρ)
    (τ : ℝ) (j : Fin J) (v : Euclidean 2) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (x : Euclidean (m + 1)) (i : Fin (m + 1)) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * (ψ (carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * (D₀).mask ((2 : ℝ) ^ j.val • θ) *
        (D₀).amplitude (((j, carrierSamplingEquiv (s, v)), (2 : ℝ) ^ j.val • θ), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
          angular highPass ψ j.val v 0 x (fullInputCoordinates m (s, θ)) i := by
  rw [correctedTransportNormalAmplitude_literal]
  by_cases hz : ψ (carrierSamplingEquiv (s, v)) = 0
  · simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul, PiLp.zero_apply]
  change (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * _ * _ *
    detectorMask angular highPass _ * (D₀).amplitude _ i = _
  rw [leadingCrossTransportKernelData_amplitude T Q F row col Φ Y χ B r κ C z₀ hρ
    hκc hA₀ hC hP hcarrier (detectorMask angular highPass) hd Md hMd hdb J τ]
  have hn := measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
    (fun z x ξ ↦ correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ
      τ (0, x, WithLp.toLp 2 z, ξ))
    (fun z : Point ↦ extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z))
    (fun _ ↦ 0) (detectorMask angular highPass) j (carrierSamplingEquiv (s, v))
    (ψ (carrierSamplingEquiv (s, v))) x θ i
  simp only [Nat.add_sub_cancel] at hn
  rw [hn]
  simp only [normalizedMeasuredAmplitude, normalizedMask, PiLp.smul_apply, smul_eq_mul,
    ← carrierParameters_eq_sampling, extendedRetainedCarrier_eq T z₀ hρ (hψ s v hz),
    mul_zero, zero_mul, zero_smul, add_zero]
  congr 1
  ring

end JanetCartan.Sampling.CorrectedTransport
