module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.RetainedEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.WeightedColumnNormal

/-!
# The actual retained transport kernel

Construct the zero endpoint from the original phase differential and the
zero principal polynomial. The global extensions only provide continuous
columns; their plateaus recover the original formulas. The consumer is the
spectator integral in `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal Topology
namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
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
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ‖ ≤ M)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular highPass η‖ ≤ B)

/-- The extended canonical phase differential used by the actual transport
kernel. It is a differential, rather than evaluation of the singular nonzero
quotient at zero (`app:ch_waves:eq:colored-normal-comparison`). -/
def retainedTransportPhase
    (q : ((Fin J × Point) × Euclidean (m + 1 - 1)) × Euclidean (m + 1)) : ℝ :=
  fderiv ℝ (extendedRetainedPhase T Q q.2)
    (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.1.1.2)) q.1.2

include hP hcarrier in
/-- Joint continuity of the actual transport phase follows from the proved
smooth phase and carrier extensions. This provides continuous full-output
columns for `app:ch_waves:eq:colored-normal-comparison`. -/
theorem continuous_retainedTransportPhase :
    Continuous (retainedTransportPhase (J := J) T Q a hρ) := by
  have hd := (contDiff_extendedRetainedPhase T Q).continuous_fderiv (by simp)
  have hz := (contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).continuous
  have heq (x : Euclidean (m + 1)) (ξ : Euclidean (m + 1 - 1)) :
      fderiv ℝ (extendedRetainedPhase T Q x) ξ =
        (fderiv ℝ (Function.uncurry (extendedRetainedPhase T Q)) (x, ξ)).comp
          (ContinuousLinearMap.inr ℝ (Euclidean (m + 1)) (Euclidean (m + 1 - 1))) := by
    exact (((contDiff_extendedRetainedPhase T Q).differentiable (by simp) _).hasFDerivAt.comp ξ
      ((hasFDerivAt_const x ξ).prodMk (hasFDerivAt_id ξ))).fderiv
  change Continuous (fun q : ((Fin J × Point) × Euclidean (m + 1 - 1)) × Euclidean (m + 1) ↦
    fderiv ℝ (extendedRetainedPhase T Q q.2)
      (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.1.1.2)) q.1.2)
  simp_rw [heq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  exact (hd.comp (continuous_snd.prodMk (hz.comp (by fun_prop)))).clm_apply
    (continuous_const.prodMk (by fun_prop))

/-- A continuous band kernel for the SAME retained zero polynomial and
canonical phase. Only the already proved global scalar polynomial smoothness
and bound are used to construct its columns; no normal estimate is a field
(`app:ch_waves:eq:colored-normal-comparison`). -/
def retainedTransportKernelData : BandKernelData (Fin J × Point) (m + 1) :=
  let ζ := fun z : Point ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z)
  let A := fun (z : Point) (x : Euclidean (m + 1)) (_ : Euclidean (m + 1 - 1)) ↦
    supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      0 (WithLp.toLp 2 z) x (ζ z)
  let hζ : Continuous ζ :=
    (contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).continuous.comp (by fun_prop)
  let D := bandKernelData (J := J) (fun _ _ _ ↦ (0 : ℝ)) A ζ (fun _ ↦ 1)
    (detectorMask angular highPass) continuous_const
    (hs.continuous.comp (f := fun q : (Point × Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦
      (0, q.1.2, WithLp.toLp 2 q.1.1, ζ q.1.1)) (by fun_prop))
    hζ continuous_const (fun _ ↦ one_ne_zero)
    (contDiff_detectorMask angular highPass ha hH hH₀).continuous
    (closedBall a.1 ρ) (isCompact_closedBall _ _)
    (fun z x _ hx ↦ supportedMeasuredDerivativePolynomial_eq_zero_off_physical
      T Q F row col Φ Y r measurement χ a hρ 0 (WithLp.toLp 2 z) x (ζ z) hx)
    M B hM hB (fun z x _ ↦ hb 0 (by norm_num) (WithLp.toLp 2 z) x (ζ z)) hdB
  { D with
    phase := retainedTransportPhase T Q a hρ
    phase_continuous := continuous_retainedTransportPhase T Q a hρ hP hcarrier }

/-- The transport amplitude is the literal zero polynomial at the retained
carrier, with the original smooth radial band and Fourier scalar. No sharp
Hilbert indicator enters the amplitude
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedTransportKernelData_amplitude :
    (retainedTransportKernelData (J := J) T Q F row col Φ Y r measurement χ a hρ hP
      hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB).amplitude =
      measuredBandAmplitude
        (fun z : Point ↦ supportedMeasuredDerivativePolynomial T Q F row col Φ Y r
          measurement χ a hρ 0 (WithLp.toLp 2 z))
        (fun z ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z))
        (fun _ ↦ 0) := by
  funext q
  simp only [retainedTransportKernelData, bandKernelData, measuredBandAmplitude,
    zero_smul, add_zero]

/-- On a nonzero retained coefficient the extension plateau identifies the
transport phase with the SAME canonical zero phase, including its actual
`2^j` normalization (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedTransportPhase_eq_on_support
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (ψ : Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (j : Fin J) (v : Euclidean 2) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (x : Euclidean (m + 1))
    (hn : supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
      angular highPass ψ j.val v 0 x (fullInputCoordinates m (s, θ)) ≠ 0) :
    retainedTransportPhase T Q a hρ (((j, carrierSamplingEquiv (s, v)),
      (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * normalizedFullPhase T Q v 0 x
        (canonicalInputCoordinates T (fullInputCoordinates m (s, θ))) := by
  obtain ⟨hx, hz, _, _⟩ := supportedMeasuredNormalAmplitude_nonzero
    T Q F row col Φ Y r measurement χ a hρ angular highPass ψ j.val v 0 x s θ hn
  have hzg := hψgraph s v hz
  have hzc : carrierParameters (v, s) ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hzg
    exact closedBall_subset_closedBall (by linarith) hzg.1
  have hbase : (x, T.reference.spatialPatch (carrierParameters (v, s))) ∈
      phaseDomain T := by
    have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
      (retained_shift_mem_plateau T a (hχ hx) hzg (d := 0) (by simp; positivity)))
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
  rw [retainedTransportPhase, ← carrierParameters_eq_sampling,
    extendedRetainedCarrier_eq T a.2.1 hρ hzc, heq,
    normalizedFullPhase_canonicalInputCoordinates_zero, map_smul]
  rfl

/-- The transport coefficient has the SAME normalized zero amplitude,
including the Fourier scalar and transverse square-root Jacobian. This is
an algebraic identity of the original measured polynomial
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedTransportKernelData_amplitude_normalization
    (ψ : Point → ℝ)
    (hψgraph : ∀ s v, ψ (carrierSamplingEquiv (s, v)) ≠ 0 →
      (carrierParameters (v, s), T.reference.spatialPatch (carrierParameters (v, s))) ∈
        closedBall a.2 (ρ / 4))
    (j : Fin J) (v : Euclidean 2) (s : ℝ) (θ : Euclidean (m + 1 - 1))
    (x : Euclidean (m + 1)) (i : Fin (m + 1)) :
    let D₀ := retainedTransportKernelData (J := J) T Q F row col Φ Y r measurement χ a hρ hP
      hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * (ψ (carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * D₀.mask ((2 : ℝ) ^ j.val • θ) *
        D₀.amplitude (((j, carrierSamplingEquiv (s, v)), (2 : ℝ) ^ j.val • θ), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        supportedMeasuredNormalAmplitude T Q F row col Φ Y r measurement χ a hρ
          angular highPass ψ j.val v 0 x (fullInputCoordinates m (s, θ)) i := by
  intro D₀
  have heq := supportedMeasuredNormalAmplitude_eq_normalized
    T Q F row col Φ Y r measurement χ a hρ angular highPass ψ 0 j.val v x s θ
  simp only [zero_mul] at heq
  rw [heq]
  by_cases hz : ψ (carrierSamplingEquiv (s, v)) = 0
  · simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul,
      normalizedMeasuredAmplitude, zero_smul, PiLp.zero_apply]
  · have hzc : carrierParameters (v, s) ∈ closedBall a.2.1 ρ := by
      have hzg := hψgraph s v hz
      rw [← closedBall_prod_same] at hzg
      exact closedBall_subset_closedBall (by linarith) hzg.1
    change (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * _ * _ *
      detectorMask angular highPass _ * D₀.amplitude _ i = _
    dsimp only [D₀]
    rw [retainedTransportKernelData_amplitude]
    have hnorm := measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
      (fun z : Point ↦ supportedMeasuredDerivativePolynomial T Q F row col Φ Y r
        measurement χ a hρ 0 (WithLp.toLp 2 z))
      (fun z ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z))
      (fun _ ↦ 0) (detectorMask angular highPass) j (carrierSamplingEquiv (s, v))
      (ψ (carrierSamplingEquiv (s, v))) x θ i
    simp only [Nat.add_sub_cancel] at hnorm
    rw [hnorm]
    simp only [normalizedMeasuredAmplitude]
    rw [← carrierParameters_eq_sampling, extendedRetainedCarrier_eq T a.2.1 hρ hzc]

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
