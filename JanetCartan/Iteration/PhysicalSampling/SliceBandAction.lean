module

public import JanetCartan.Iteration.PhysicalSampling.SlicePhase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawBandBounds

/-!
# Scalar single-channel action equals the original physical band action

The equality retains all original smooth masks, the half derivative, Fourier
normalization and actual wide-band input. Only the scalar support is used to
remove the phase extensions. The sharp sampling bound therefore follows from
the constructed single-channel operator, not from a kernel norm assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSampling

open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry
open LeadingWave.FullModulation FullPhaseCharts FullPhaseCharts.ActualPhase Sampling.MeasuredAmplitude
open RawInputPartition RawPrimary.MaskProfiles PhysicalMean NormalComparison

/-- The raw scalar amplitude has precisely the original normalized mask. -/
theorem rawScalarSliceBandAmplitude_eq_channel {n : ℕ} (hn : 1 ≤ n)
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (ζ : Euclidean (n - 1)) (τ : ℝ) (j : ℕ)
    (q : ℝ × Euclidean (n - 1)) (θ : Euclidean (n - 1)) :
    rawSliceBandAmplitude (n := n)
      (fun q _ ↦ scalarAuxiliaryAmplitude hn χ () (adaptedPhysicalCoordinates sec q) 0)
      (fun _ ↦ 1) ζ τ (weightedRadialBand (detectorMask angular H) j) j q θ =
        scalarSliceChannelAmplitude sec χ angular H hn j (q, θ) := by
  ext i
  simp only [rawSliceBandAmplitude, scalarAuxiliaryAmplitude, scalarSliceChannelAmplitude,
    scalarSliceAmplitude, normalizedMask, Complex.ofReal_one, one_mul,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

variable {m : ℕ}
variable {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- The constructed scalar slice integral is exactly the normalized original
raw integral. Nonzero masks are used only to verify the retained phase plateau;
zero-mask regions remain identical without any support assumption there. -/
theorem scalarSliceBandIntegral_eq_retained_raw
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (angular : Euclidean ((m + 1) - 1) → ℂ) (H : Euclidean ((m + 1) - 1) → ℝ)
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {σ : ℝ} (hσ : 0 < σ) (hphase : closedBall center (2 * σ) ⊆ domain T)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hχa : tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4))
    (hχσ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (σ / 2))
    (z : Euclidean 3)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (hzg : (z, T.reference.spatialPatch z) ∈ closedBall center.2 (σ / 4))
    {τ : ℝ} (hτ : τ ≠ 0) (j : ℕ)
    (hε : τ * (2 : ℝ) ^ j ∈ Icc 0 e) (hscale : |τ * (2 : ℝ) ^ j| ≤ σ / 8)
    (f : WideBandL2 (m + 1) j) (q : ℝ × Euclidean ((m + 1) - 1)) :
    normalOperatorScale (m + 1) ((2 : ℝ) ^ j) •
      (∫ θ in wideBand (m + 1) 0,
        (oscillatoryFactor ((2 : ℝ) ^ j)
          (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)
            (τ * (2 : ℝ) ^ j, q, θ)) * wideBandDilation (m + 1) j f θ) •
          scalarSliceChannelAmplitude T.data.adapted χ angular H (Nat.succ_le_succ (Nat.zero_le m)) j (q, θ)) =
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        rawSliceBandIntegral
          (fun q η ↦ extendedRetainedPhase T Q (adaptedPhysicalCoordinates T.data.adapted q) η)
          (fun q _ ↦ scalarAuxiliaryAmplitude (Nat.succ_le_succ (Nat.zero_le m)) χ ()
            (adaptedPhysicalCoordinates T.data.adapted q) 0)
          (fun _ ↦ 1) (extendedRetainedCarrier T center.2.1 hσ z) τ
          (weightedRadialBand (detectorMask angular H) j) j f q := by
  rw [normalized_rawSliceBandIntegral_weighted (Nat.succ_le_succ (Nat.zero_le m)) _ _ _ _ hτ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [rawScalarSliceBandAmplitude_eq_channel]
  by_cases hx : χ (adaptedPhysicalCoordinates T.data.adapted q) = 0
  · have hz : scalarSliceChannelAmplitude T.data.adapted χ angular H (Nat.succ_le_succ (Nat.zero_le m)) j (q, θ) = 0 := by
      ext i
      simp only [scalarSliceChannelAmplitude, scalarSliceAmplitude, PiLp.toLp_apply,
        hx, Complex.ofReal_zero, mul_zero, zero_mul, PiLp.zero_apply]
    rw [hz, smul_zero, smul_zero]
  by_cases hm : normalizedMask angular H j θ = 0
  · have hz : scalarSliceChannelAmplitude T.data.adapted χ angular H (Nat.succ_le_succ (Nat.zero_le m)) j (q, θ) = 0 := by
      ext i
      simp only [scalarSliceChannelAmplitude, scalarSliceAmplitude, PiLp.toLp_apply,
        hm, zero_mul, PiLp.zero_apply]
    rw [hz, smul_zero, smul_zero]
  have hθ : ‖θ‖ ≤ 2 := mem_closedBall_zero_iff.mp (support_normalizedMask_subset angular H j hm)
  rw [scalarSlicePhase_eq_retained T Q center hσ hphase ha haR he heb z hb hzg hε
    (mul_ne_zero hτ (by positivity)) hscale q θ (hχa (subset_tsupport _ hx)) (hχσ hx) hθ]

end JanetCartan.PhysicalSampling
