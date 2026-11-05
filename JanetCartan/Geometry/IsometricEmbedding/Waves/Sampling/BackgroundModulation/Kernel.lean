module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.NormalizedAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawBandBounds

/-!
# The literal retained background-modulation sampling kernel

The actual Hermitian product, its proved supported budget and the original
phase/carrier extensions instantiate `RawKernel.bandKernelData`. The carrier,
physical, angular and high-pass cutoffs, Fourier scalar and Lebesgue measures
remain literal. The parent applies the retained profile producer below to
supply the amplitude bound before varying fields or band ceilings.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.BackgroundModulation
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open MeasuredAmplitude
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition

open FullPhaseCharts FullNormalGeometry.PhaseJets
open MeanNormalBound.NormalizedFullPhase ContinuumRow
section Normalization
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
  (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
  (ψ : SeparatedSampling.Point → ℝ)

/-- The normalized extended raw coefficient equals the supported normal
homotopy at `ε = τ 2^j`, including at zero. No inverse-frequency formula or
differentiability hypothesis is needed for this polynomial identity
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedBackgroundModulationNormalAmplitude_eq_normalized
    (τ : ℝ) (j : ℕ) (v : Euclidean 2) (x : Euclidean (m + 1))
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) :
    supportedBackgroundModulationNormalAmplitude T Q F row col Φ Y r χ a hρ
      angular H ψ j v (τ * (2 : ℝ) ^ j) x (fullInputCoordinates m (s, θ)) =
      normalizedMeasuredAmplitude
        (supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ τ)
        T.reference.spatialPatch (fun _ ↦ τ) (detectorMask (n := m + 1) angular H) j
        (carrierParameters (v, s)) (ψ (carrierSamplingEquiv (s, v))) x θ := by
  have hp : ((2 : ℝ) ^ j)⁻¹ * (τ * (2 : ℝ) ^ j) = τ := by
    field_simp
  simp only [supportedBackgroundModulationNormalAmplitude, normalizedMeasuredPullback,
    normalizedRetainedMask, normalizedRetainedPoint, inputCoordinates_apply,
    adapted_canonicalInputCoordinates, hp, supportedBackgroundModulationPolynomial,
    normalizedMeasuredAmplitude, normalizedMask, mul_assoc]

/-- The original modulated-slot cutoff gives fixed physical support of
the actual Hermitian product (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedBackgroundModulationPolynomial_eq_zero_off_physical
    (τ : ℝ) (z : Euclidean 3) (x : Euclidean (m + 1)) (ξ : Euclidean (m + 1 - 1))
    (hx : x ∉ closedBall a.1 ρ) :
    supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ τ z x ξ = 0 := by
  have hw : (x, (z, ξ)) ∉ closedBall a (3 * ρ / 4) := by
    intro hw
    rw [← closedBall_prod_same] at hw
    exact hx (closedBall_subset_closedBall (by linarith) hw.1)
  exact (supportedBackgroundModulationPolynomial_eventually_zero
    T Q F row col Φ Y r χ a hρ τ (x, (z, ξ)) hw).eq_of_nhds

end Normalization

variable {m N J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
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
  (τ : (Fin 3 → Fin (p + 1)) → ℝ)
  (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1) (hτ₀ : ∀ color, τ color ≠ 0)

/-- Concrete `BandKernelData` for the measured retained raw family, including
every color on the SAME original sampling point space. The fixed physical
support and coefficient bound precede all frequencies and band ceilings
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def retainedBackgroundModulationKernelData :
    BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point)) (m + 1) :=
  bandKernelData
    (fun _ : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦ extendedRetainedPhase T Q)
    (fun q ↦ supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
      (τ q.1) (WithLp.toLp 2 q.2))
    (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
    (fun q ↦ τ q.1) (detectorMask angular highPass)
    ((contDiff_extendedRetainedPhase T Q).continuous.comp
      (f := fun q : (((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point) ×
        Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦ (q.1.2, q.2)) (by fun_prop))
    (hs.continuous.comp (f := fun q : (((Fin 3 → Fin (p + 1)) × SeparatedSampling.Point) ×
        Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦
      (τ q.1.1.1, q.1.2, WithLp.toLp 2 q.1.1.2, q.2)) (by fun_prop))
    ((contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).continuous.comp (by fun_prop))
    (by fun_prop) (fun q ↦ hτ₀ q.1)
    (contDiff_detectorMask angular highPass ha hH hH₀).continuous
    (closedBall a.1 ρ) (isCompact_closedBall _ _)
    (fun q x ξ hx ↦ supportedBackgroundModulationPolynomial_eq_zero_off_physical
      T Q F row col Φ Y r χ a hρ (τ q.1) (WithLp.toLp 2 q.2) x ξ hx)
    M B hM hB (fun q x ξ ↦ hb (τ q.1) (hτ q.1) (WithLp.toLp 2 q.2) x ξ) hdB

local notation "D" => retainedBackgroundModulationKernelData (J := J) T Q F row col Φ Y r χ
  a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀

/-- The kernel constant of the SAME constructed raw family is independent
of colors, radial labels, history scale and band count. This is the literal
`hkernel` constant, once the already proved polynomial budget is instantiated
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem retainedBackgroundModulationKernelData_squaredKernelConstant :
    (D).squaredKernelConstant = volume.real (closedBall a.1 ρ) * B ^ 2 *
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * M) ^ 2 *
        RawInputRealization.unitBallVolume (m + 1) := rfl

/-- Literal formula for the constructed kernel, before removing its smooth
extensions. It keeps the original Fourier scalar, half derivative and smooth
wide band; neither sharp refinement indicator appears in the amplitude
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedBackgroundModulationKernelData_kernel (j : Fin J)
    (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (D).kernel (j, (color, z)) η x =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (detectorMask angular highPass) j.val η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
            (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
            supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
              (τ color) (WithLp.toLp 2 z) x
              (extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 z) + (τ color) • η)) := by
  unfold retainedBackgroundModulationKernelData
  apply bandKernelData_kernel

/-- Remove every auxiliary extension from the actual measured kernel.
The original raw phase, detector, polynomial, half derivative and Fourier
scalar occur literally on the right. The carrier and physical conditions
are the SAME buffered refinement and measurement support used to construct
the normal amplitude (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedBackgroundModulationKernelData_kernel_eq_raw
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
    (hz : (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
      closedBall a.2 (ρ / 4))
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1))
    (hd : ‖(τ color) • η‖ ≤ ρ / 4) :
    (D).kernel (j, (color, z)) η x =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (detectorMask angular highPass) j.val η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
            (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
            measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
              (τ color) (WithLp.toLp 2 z) x
              (T.reference.spatialPatch (WithLp.toLp 2 z) + (τ color) • η)) := by
  rw [retainedBackgroundModulationKernelData_kernel]
  have hz' : WithLp.toLp 2 z ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hz
    exact closedBall_subset_closedBall (by linarith) hz.1
  rw [extendedRetainedCarrier_eq T a.2.1 hρ hz',
    supportedBackgroundModulationPolynomial_eq_raw T Q F row col Φ Y r χ
      a hρ hχ hz (τ color) x ((τ color) • η) hd]
  by_cases hx : χ x = 0
  · simp only [measuredBackgroundModulationPolynomial, hx, Complex.ofReal_zero, zero_smul,
      smul_zero]
  · rw [extendedRetainedPhase_difference_eq T Q a hρ hphase (hχ hx) hz (τ color) η hd]

/-- The source's single band-scale buffer removes the extensions for ALL
input covectors. Outside the original smooth wide band both literal kernels
vanish; no sharp shell indicator is differentiated
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedBackgroundModulationKernelData_kernel_eq_raw_of_bandScale
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
    (hz : (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
      closedBall a.2 (ρ / 4))
    (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (D).kernel (j, (color, z)) η x =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand (detectorMask angular highPass) j.val η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (phase T Q)
            (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) x η : ℂ)) •
            measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
              (τ color) (WithLp.toLp 2 z) x
              (T.reference.spatialPatch (WithLp.toLp 2 z) + (τ color) • η)) := by
  by_cases hη : η ∈ wideBand (m + 1) j.val
  · apply retainedBackgroundModulationKernelData_kernel_eq_raw
      T Q F row col Φ Y r χ a hρ hP hcarrier hs M hM hb
      angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ j color z hz x η
    have hnorm : ‖η‖ ≤ 2 * (2 : ℝ) ^ j.val := by
      have hu := hη.1
      simp only [mem_closedBall, dist_zero_right, dyadicScale] at hu
      linarith
    calc
      ‖(τ color) • η‖ = |τ color| * ‖η‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |τ color| * (2 * (2 : ℝ) ^ j.val) :=
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ = (|τ color| * (2 : ℝ) ^ j.val) * 2 := by ring
      _ ≤ (ρ / 8) * 2 := mul_le_mul_of_nonneg_right hscale (by norm_num)
      _ = ρ / 4 := by ring
  · rw [retainedBackgroundModulationKernelData_kernel,
      weightedRadialBand_eq_zero_off_wideBand (detectorMask angular highPass) hη]
    simp only [mul_zero, zero_smul, smul_zero]

/-- The SAME constructed kernel supplies the amplitude equation used by
`LiteralMeanBound.exists_source_mean_bound`. This identifies the nonzero
measured normal data, with the transverse square-root Jacobian and the exact
Fourier scalar, for every physical position and both quadratures
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem retainedBackgroundModulationKernelData_amplitude_normalization
    (ψ : SeparatedSampling.Point → ℝ)
    (hψ : ∀ s v, ψ (ContinuumRow.carrierSamplingEquiv (s, v)) ≠ 0 →
      (FullPhaseCharts.carrierParameters (v, s),
        T.reference.spatialPatch (FullPhaseCharts.carrierParameters (v, s))) ∈
          closedBall a.2 (ρ / 4))
    (j : Fin J) (color : Fin 3 → Fin (p + 1)) (v : Euclidean 2)
    (s : ℝ) (θ : Euclidean (m + 1 - 1)) (x : Euclidean (m + 1)) (i : Fin (m + 1)) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) *
      (ψ (ContinuumRow.carrierSamplingEquiv (s, v)) : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * (D).mask ((2 : ℝ) ^ j.val • θ) *
      (D).amplitude (((j, (color, ContinuumRow.carrierSamplingEquiv (s, v))),
        (2 : ℝ) ^ j.val • θ), x) i =
      (NormalComparison.normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
        supportedBackgroundModulationNormalAmplitude T Q F row col Φ Y r χ a hρ
          angular highPass ψ j.val v ((τ color) * (2 : ℝ) ^ j.val) x
            (MeanNormalBound.NormalizedFullPhase.fullInputCoordinates m (s, θ)) i := by
  rw [supportedBackgroundModulationNormalAmplitude_eq_normalized T Q F row col Φ Y r χ
    a hρ angular highPass ψ (τ color) j.val v x s θ]
  by_cases hz : ψ (ContinuumRow.carrierSamplingEquiv (s, v)) = 0
  · simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul,
      normalizedMeasuredAmplitude, zero_smul, PiLp.zero_apply]
  · have hzg := hψ s v hz
    have hzc : FullPhaseCharts.carrierParameters (v, s) ∈ closedBall a.2.1 ρ := by
      rw [← closedBall_prod_same] at hzg
      exact closedBall_subset_closedBall (by linarith) hzg.1
    change (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) * _ * _ *
        detectorMask angular highPass _ *
          measuredBandAmplitude
            (fun q : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦
              supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
                (τ q.1) (WithLp.toLp 2 q.2))
            (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
            (fun q ↦ τ q.1)
            (((j, (color, ContinuumRow.carrierSamplingEquiv (s, v))),
              (2 : ℝ) ^ j.val • θ), x) i = _
    have hnorm := measuredBandAmplitude_normalization (by omega : 1 ≤ m + 1)
      (fun q : (Fin 3 → Fin (p + 1)) × SeparatedSampling.Point ↦
        supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
          (τ q.1) (WithLp.toLp 2 q.2))
      (fun q ↦ extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2))
      (fun q ↦ τ q.1) (detectorMask angular highPass) j
      (color, ContinuumRow.carrierSamplingEquiv (s, v))
      (ψ (ContinuumRow.carrierSamplingEquiv (s, v))) x θ i
    simp only [Nat.add_sub_cancel] at hnorm
    rw [hnorm]
    simp only [normalizedMeasuredAmplitude]
    rw [← carrierParameters_eq_sampling,
      extendedRetainedCarrier_eq T a.2.1 hρ hzc]

end JanetCartan.Sampling.BackgroundModulation
