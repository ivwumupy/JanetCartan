module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.WideBandIntegral

/-!
# The actual retained sampling channels on original wide-band data

Remove the fixed extensions under the original band buffer and identify each
constructed channel with its measured raw polynomial integral. This is the
operator-to-wave connection consumed by the sharp sampling estimate; both
refined shells retain the same smooth band and the same full output.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition
open MeanNormalBound RawPrimary.SliceBounds

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
  (τ : (Fin 3 → Fin (p + 1)) → ℝ)
  (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ
  a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀

variable (hphase : closedBall a (2 * ρ) ⊆ domain T)
  (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
  (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
  (hz : (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
    closedBall a.2 (ρ / 4))

include hphase hχ hz in
/-- The constructed wide channel has exactly the original measured raw
polynomial integral, including its physical Fourier scalar. Every extension
is removed by the proved same-band buffer; this is equality for arbitrary
Lebesgue L² input, not just smooth data
(`app:ch_waves:eq:individual-representation`). -/
theorem retainedMeasuredKernelData_wideOperator_ae_polynomial
    (j : Fin J) (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (f : WideBandL2 (m + 1) j.val) :
    wideBandKernelOperator D j.val (j, (color, z)) f =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        rawSliceBandIntegral (phase T Q)
          (fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
            (τ color) (WithLp.toLp 2 z))
          (fun _ ↦ 1) (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color)
          (weightedRadialBand (detectorMask angular highPass) j.val) j.val f x := by
  have hsupp : ∀ η ∉ wideBand (m + 1) j.val, ∀ x, (D).kernel (j, (color, z)) η x = 0 := by
    intro η hη x
    rw [retainedMeasuredKernelData_kernel]
    simp only [weightedRadialBand_eq_zero_off_wideBand (detectorMask angular highPass) hη,
      mul_zero, zero_smul, smul_zero]
  refine (wideBandKernelOperator_ae_integral D j.val (j, (color, z)) hsupp f).trans
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [rawSliceBandIntegral, Complex.ofReal_one, one_smul,
    rawPrimaryDemodulatedIntegral]
  rw [← integral_smul, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun η hη ↦ by rw [hsupp η hη x, smul_zero])]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [retainedMeasuredKernelData_kernel_eq_raw_of_bandScale
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
    ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ j color z hz hscale]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  ring

include hphase hχ hz in
/-- The complete wide row uses a single literal band sum on the SAME full
input. This identity is proved from the individual constructed operators,
with no assumed bounded raw superposition (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedMeasuredKernelData_row_ae_polynomial
    (hscale : ∀ j : Fin J, |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (v : WideInput (m + 1) J) :
    wideBandKernelRow D (color, z) v =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        ∑ j : Fin J, rawSliceBandIntegral (phase T Q)
          (fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
            (τ color) (WithLp.toLp 2 z))
          (fun _ ↦ 1) (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color)
          (weightedRadialBand (detectorMask angular highPass) j.val) j.val (v j) x := by
  simp only [wideBandKernelRow, NormalPerturbation.weightedRow_apply, Real.sqrt_one,
    RCLike.ofReal_one, one_smul]
  refine (Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin J ↦ wideBandKernelOperator D j.val (j, (color, z)) (v j))).trans ?_
  have he := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦
    retainedMeasuredKernelData_wideOperator_ae_polynomial
      T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
      ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ color z hz j (hscale j) (v j))
  exact he.trans (Filter.Eventually.of_forall fun x ↦ by
    simp only [Finset.sum_apply, Finset.smul_sum])

end JanetCartan.Sampling.MeasuredAmplitude
