module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.BandAction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.WaveIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.BandInput
public import JanetCartan.Analysis.Sobolev.Local.Basic

/-!
# The measured single band and its original raw integral norm

The consumer is `UniformBandBounds`, which applies the actual canonical raw
slice producer at the original band scale. All cutoffs, tensor measurements,
half derivatives and Fourier scalars are retained.
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
open RawPrimary LeadingWave
open RawPrimary.AmplitudeGrades.Polynomial

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

variable
  {Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
  (hΩ : IsOpen Ω) (hphaseΩ : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
  (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
  (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
  (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
  (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
  {X : Set (Euclidean (m + 1))} {V : Set (Euclidean (m + 1 - 1))}
  (hζ : T.reference.spatialPatch (WithLp.toLp 2 z) ∈ V)
  (hproduct : ∀ q ∈ X ×ˢ V, (q.1, (WithLp.toLp 2 z, q.2)) ∈ Ω)
  (hχX : Function.support χ ⊆ X)

include hphase hχ hz hΩ hphaseΩ hν₀ hν₁ hV₀ hV₁ hζ hproduct hχX in
/-- Transfer the SAME single-band raw extension to the measured channel.
The single datum uses `cutoffCount (2^j)`, so even a band below the amplitude
scale retains its original ceiling. This is the literal norm connection used
in `app:ch_waves:eq:sampling-operator-bounds`. -/
theorem norm_retainedMeasuredKernelData_band_le_rawIntegral
    (j : Fin J) (hscale : |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (hshift : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ cutoffCount ((2 : ℝ) ^ j.val)),
      T.reference.spatialPatch (WithLp.toLp 2 z) + τ color • η ∈ V)
    (f : WideBandL2 (m + 1) j.val)
    (θ : Euclidean (m + 1) → ℝ)
    {R : Set (Euclidean (m + 1))}
    {u : LocalSobolev.LocalL2 R (Matrix (Fin N) (Fin (m + 1)) ℂ)}
    (e : LocalSobolev.SobolevExtension R 0 u)
    (he : e.toFun = fun x ↦ θ x •
      rawPrimaryDemodulatedIntegral (phase T Q)
        (fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r (τ color)
          (x, (WithLp.toLp 2 z, η)))
        (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color) volume
        (weightedWideDensity (detectorMask angular highPass)
          (PiLp.single 2 (⟨j.val, by rw [cutoffCount_two_pow]; omega⟩ :
            Fin (cutoffCount ((2 : ℝ) ^ j.val))) f)) x)
    (hθ : ∀ x, χ x ≠ 0 → θ x = 1)
    (hχone : ∀ x, |χ x| ≤ 1)
    {Cmeasurement : ℝ} (hCmeasurement : 0 ≤ Cmeasurement)
    (hmeasurement : ∀ x ∈ closedBall a.1 (ρ / 2), ‖measurement x‖ ≤ Cmeasurement) :
    ‖wideBandKernelOperator D j.val (j, (color, z)) f‖ ≤
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * Cmeasurement) * e.jetNorm := by
  let j' : Fin (cutoffCount ((2 : ℝ) ^ j.val)) :=
    ⟨j.val, by rw [cutoffCount_two_pow]; omega⟩
  have hd := (contDiff_detectorMask angular highPass ha hH hH₀).continuous.measurable
  let w := e.memLp_fun.toLp e.toFun
  have hw : ‖w‖ = e.jetNorm := by
    rw [LocalSobolev.SobolevExtension.jetNorm_zero]
    exact Lp.norm_toLp e.toFun e.memLp_fun
  have hraw := retainedMeasuredKernelData_wideOperator_ae_polynomial
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
    ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ color z hz j hscale f
  let cFourier : ℝ := (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2)
  have hFourier : 0 < cFourier := Real.rpow_pos_of_pos (by positivity) _
  have hbnd : ‖wideBandKernelOperator D j.val (j, (color, z)) f‖ ≤
      (cFourier * Cmeasurement) * ‖w‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hraw, e.memLp_fun.coeFn_toLp] with x hx hwx
    have hm := rawSliceBandIntegral_measuredPolynomial
      T Q F row col Φ Y r measurement χ hΩ hphaseΩ hν₀ hν₁ hV₀ hV₁ (hτ₀ color)
      (WithLp.toLp 2 z) hζ hproduct hshift hd hdB j' f (x := x) (fun hn ↦ hχX hn)
    rw [hx, hm]
    by_cases hcx : χ x = 0
    · simp only [hcx, Complex.ofReal_zero, zero_smul, smul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg hFourier.le hCmeasurement) (norm_nonneg _)
    have heq : rawSliceBandIntegral (phase T Q)
        (fun x η ↦ fullDerivativeAmplitude T Q F row col Φ Y r (τ color)
          (x, (WithLp.toLp 2 z, η))) (fun _ ↦ 1)
        (T.reference.spatialPatch (WithLp.toLp 2 z)) (τ color)
        (weightedRadialBand (detectorMask angular highPass) j.val) j.val f x = e.toFun x := by
      rw [rawSliceBandIntegral_eq_singleDensity _ _ _ _ _ hd hdB j' f,
        Complex.ofReal_one, one_smul, he]
      dsimp only
      rw [hθ x hcx, one_smul]
    rw [heq]
    have hm' : ‖measurement x (e.toFun x)‖ ≤ Cmeasurement * ‖e.toFun x‖ :=
      (measurement x).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (hmeasurement x (hχ hcx)) (norm_nonneg _))
    change ‖cFourier • ((χ x : ℂ) • measurement x (e.toFun x))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hFourier,
      norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ cFourier * (1 * (Cmeasurement * ‖e.toFun x‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hχone x) hm' (norm_nonneg _) zero_le_one) hFourier.le
      _ = (cFourier * Cmeasurement) * ‖w x‖ := by rw [hwx]; ring
  exact hbnd.trans_eq (by rw [hw])

end JanetCartan.Sampling.MeasuredAmplitude
