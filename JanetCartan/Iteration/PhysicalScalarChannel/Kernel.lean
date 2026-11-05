module

public import JanetCartan.Iteration.PhysicalScalarChannel.BareNormalization
public import JanetCartan.Iteration.PhysicalSampling.SliceBandAction

/-!
# The actual normalized scalar channel kernel

This is the original canonical finite-parameter phase and scalar cutoff, with
transverse Fourier normalization. The full-band normal theorem applies to its
entire direct-sum input. The inverse-half multiplier removes only the annular
half weight, without altering any original mask or retained phase.
Consumers: the individual `q - 1/2` moment following
`app:ch_mean_pairs:eq:raw-adjoint-moments`, and the fixed-carrier forward
estimate in `app:ch_mean_pairs:eq:block-fields`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalScalarChannel

open NormalComparison SingleChannel ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry RawPrimary.MaskProfiles RawInputPartition
open FullPhaseCharts.ActualPhase PhysicalSampling PhysicalMean

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual original scalar kernel with transverse, rather than physical,
normalization. The sole extra factor on returning to physical coordinates is
`(2π)^(-1/2)`, proved in `BareNormalization`. -/
def scalarFullBandChannelKernel (hn : 1 ≤ n) (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (z : Euclidean 3) (j : ℕ) (ε : ℝ)
    (x : ℝ × Euclidean (n - 1)) (θ : Euclidean (n - 1)) : EuclideanSpace ℂ (Fin n) :=
  ((normalOperatorScale (n - 1) ((2 : ℝ) ^ j) : ℂ) * oscillatoryFactor ((2 : ℝ) ^ j)
    (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z) (ε, x, θ))) •
      scalarSliceChannelAmplitude T.data.adapted χ angular H hn j (x, θ)

/-- All kernel construction premises are proved on the SAME retained canonical
slice geometry, before invoking the full dyadic normal bound. -/
theorem scalarFullBandChannelKernel_properties (hn : 1 ≤ n)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (z : Euclidean 3)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) (hH : ContDiff ℝ ∞ H)
    (hχ : tsupport (χ : Euclidean n → ℝ) ⊆ closedBall 0 (a / 4))
    (j : ℕ) {ε : ℝ} (hε : ε ∈ Icc 0 e) :
    Continuous (Function.uncurry (scalarFullBandChannelKernel T Q hn χ angular H z j ε)) ∧
    HasCompactSupport (Function.uncurry (scalarFullBandChannelKernel T Q hn χ angular H z j ε)) ∧
    (∀ t ∉ Ioo (-a) a, ∀ y θ, scalarFullBandChannelKernel T Q hn χ angular H z j ε (t, y) θ = 0) := by
  let amp := scalarSliceChannelAmplitude T.data.adapted χ angular H hn j
  have hamp : Continuous amp :=
    (PiLp.continuous_toLp 2 _).comp
      ((contDiff_scalarSliceAmplitude T.data.adapted χ angular H hang hH hn j).continuous.comp
        (by fun_prop))
  have hsupport := scalarSliceChannelAmplitude_support T.data.adapted χ angular H hn hχ j
  have hcompact : HasCompactSupport amp :=
    (isCompact_closedBall (0 : ℝ × Euclidean (n - 1)) (a / 4)).prod
      (isCompact_closedBall 0 2) |>.of_isClosed_subset isClosed_closure hsupport
  have hsub : tsupport (Function.uncurry
      (scalarFullBandChannelKernel T Q hn χ angular H z j ε)) ⊆ tsupport amp :=
    tsupport_smul_subset_right _ _
  have hφ : ∀ q ∈ tsupport amp, ContinuousAt (fun q :
      (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        rawSlicePhaseExtension (canonicalBasePhase T Q)
          (T.reference.spatialPatch z) (ε, q.1, q.2)) q := by
    intro q hq
    have hsup := hsupport hq
    have hnorm : ‖q.1‖ ≤ a / 4 := mem_closedBall_zero_iff.mp hsup.1
    have htime : q.1.1 ∈ Ioo (-a) a := by
      have hh := (norm_fst_le q.1).trans hnorm
      rw [Real.norm_eq_abs] at hh
      exact abs_lt.mp (hh.trans_lt (by linarith : a / 4 < a))
    have hy : q.1.2 ∈ ball (0 : Euclidean (n - 1)) (2 * a) :=
      mem_ball_zero_iff.mpr ((norm_snd_le q.1).trans hnorm |>.trans_lt (by linarith))
    have hθ : q.2 ∈ sliceInputExtension n :=
      closedBall_subset_ball (by norm_num : (2 : ℝ) < 4) hsup.2
    have hε' : ε ∈ sliceParameterDomain e :=
      ⟨by linarith [hε.1], by linarith [hε.2]⟩
    have hmem : (ε, q.1.2, q.2) ∈
        sliceParameterDomain e ×ˢ sliceExtensionDomain n a := ⟨hε', hy, hθ⟩
    have hm := sliceExtensionDomain_mapsTo_shiftDomain T ha htime hmem
    change (ε, q.1, q.2) ∈ sliceShiftDomain T a e at hm
    exact ((canonicalSlicePhase_smooth_on_shiftDomain T Q z haR he heb hb).continuousOn.continuousAt
      ((isOpen_sliceShiftDomain T a e).mem_nhds hm)).comp (by fun_prop)
  refine ⟨?_, hcompact.of_isClosed_subset isClosed_closure hsub, ?_⟩
  · apply continuous_of_tsupport
    intro q hq
    have hq' := hφ q (hsub hq)
    have hc : ContinuousAt (fun q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        (normalOperatorScale (n - 1) ((2 : ℝ) ^ j) : ℂ) *
          oscillatoryFactor ((2 : ℝ) ^ j)
            (rawSlicePhaseExtension (canonicalBasePhase T Q)
              (T.reference.spatialPatch z) (ε, q.1, q.2))) q := by
      unfold oscillatoryFactor
      fun_prop
    exact hc.smul hamp.continuousAt
  · intro t ht y θ
    have hz : amp ((t, y), θ) = 0 := by
      by_contra hh
      have hs := hsupport (subset_tsupport _ hh)
      have ht' := (norm_fst_le (t, y)).trans (mem_closedBall_zero_iff.mp hs.1)
      rw [Real.norm_eq_abs] at ht'
      exact ht (abs_lt.mp (ht'.trans_lt (by linarith : a / 4 < a)))
    change _ • amp ((t, y), θ) = 0
    rw [hz, smul_zero]

/-- No normalized input outside the original buffered chart contributes to the
actual scalar kernel. This is proved from the original radial mask. -/
theorem scalarFullBandChannelKernel_eq_zero_outside_chart (hn : 1 ≤ n)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (z : Euclidean 3) (j : ℕ) (ε : ℝ) (x : ℝ × Euclidean (n - 1))
    {θ : Euclidean (n - 1)} (hθ : θ ∉ sliceInputDomain n) :
    scalarFullBandChannelKernel T Q hn χ angular H z j ε x θ = 0 := by
  have hz : normalizedMask angular H j θ = 0 := by
    by_contra hh
    have hm := support_normalizedMask_subset angular H j hh
    exact hθ (closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hm)
  ext i
  simp only [scalarFullBandChannelKernel, PiLp.smul_apply, smul_eq_mul,
    scalarSliceChannelAmplitude, scalarSliceAmplitude, hz,
    zero_mul, mul_zero, PiLp.zero_apply]

/-- The scalar normalized amplitude has only the original normalized mask and
fixed physical scalar cutoff. -/
theorem scalarSliceChannelAmplitude_eq_normalizedMask_smul (hn : 1 ≤ n)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (j : ℕ) (x : ℝ × Euclidean (n - 1)) (θ : Euclidean (n - 1)) :
    scalarSliceChannelAmplitude T.data.adapted χ angular H hn j (x, θ) =
      normalizedMask angular H j θ •
        scalarAuxiliaryAmplitude hn χ () (adaptedPhysicalCoordinates T.data.adapted x) 0 := by
  ext i
  simp only [scalarSliceChannelAmplitude, scalarSliceAmplitude, scalarAuxiliaryAmplitude,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Exact bare input action on the original unit wide band. The bounded inverse
half acts on the input, while all original masks and the actual phase remain
unchanged in the displayed integral. -/
theorem channelIntegral_bareChartInput (hn : 1 ≤ n)
    (χ : ContDiffBump (0 : Euclidean n))
    (angular : Euclidean (n - 1) → ℂ) (H : Euclidean (n - 1) → ℝ)
    (z : Euclidean 3) (j : ℕ) (ε : ℝ)
    {D : Set (Euclidean (n - 1))} (hD : D = sliceInputDomain n)
    (f : WideBandL2 n j) (x : ℝ × Euclidean (n - 1)) :
    channelIntegral (scalarFullBandChannelKernel T Q hn χ angular H z j ε)
      (bareChartInput n j D f) x =
      normalOperatorScale (n - 1) ((2 : ℝ) ^ j) •
        ∫ θ in wideBand n 0,
          ((oscillatoryFactor ((2 : ℝ) ^ j)
            (rawSlicePhaseExtension (canonicalBasePhase T Q)
              (T.reference.spatialPatch z) (ε, x, θ)) *
            weightedRadialBand (detectorMask angular H) j ((2 : ℝ) ^ j • θ)) *
            wideBandDilation n j f θ) •
              scalarAuxiliaryAmplitude hn χ () (adaptedPhysicalCoordinates T.data.adapted x) 0 := by
  let k := scalarFullBandChannelKernel T Q hn χ angular H z j ε
  have he : channelIntegral k (bareChartInput n j D f) x =
      ∫ θ in D, wideBandChartInput n j D f θ • (annularInverseHalf θ • k x θ) := by
    apply integral_congr_ae
    filter_upwards [bareChartInput_apply_ae n j D f, wideBandChartInput_apply_ae j D f]
      with θ hbare hwide
    change bareChartInput n j D f θ • k x θ = _
    rw [hbare, hwide, smul_smul, mul_comm]
  rw [he]
  dsimp only [k]
  rw [integral_wideBandChartInput j _ (fun θ hθ ↦ by
    rw [scalarFullBandChannelKernel_eq_zero_outside_chart T Q hn χ angular H z j ε x (hD ▸ hθ),
      smul_zero]), ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [scalarFullBandChannelKernel, scalarSliceChannelAmplitude_eq_normalizedMask_smul]
  simp only [smul_smul, ← Complex.coe_smul]
  congr 1
  calc
    _ = ((normalOperatorScale (n - 1) ((2 : ℝ) ^ j) : ℂ) *
        oscillatoryFactor ((2 : ℝ) ^ j)
          (rawSlicePhaseExtension (canonicalBasePhase T Q)
            (T.reference.spatialPatch z) (ε, x, θ)) * wideBandDilation n j f θ) *
        (annularInverseHalf θ * normalizedMask angular H j θ) := by ring
    _ = _ := by rw [annularInverseHalf_mul_normalizedMask]; ring

end JanetCartan.PhysicalScalarChannel
