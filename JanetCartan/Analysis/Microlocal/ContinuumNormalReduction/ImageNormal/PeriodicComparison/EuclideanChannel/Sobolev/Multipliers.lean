module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication

/-!
# Scalar H¹ factors of the Euclidean image channel

The concrete factors of `μ P J χ` in `app:ch_background:prop:bg-frame`, Step 1,
preserve the Fourier H¹ space. Compactness supplies every coefficient bound;
the frequency factors are contractions for the weighted Fourier norm. These
estimates are consumed by `euclideanChannelBlock_sobolev_one_bound`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal JanetCartan.IsometricEmbedding.Reconstruction

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- A symbol of size at most one preserves the weighted H¹ norm. This supplies
both frequency factors of the channel in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem fourierMultiplier_sobolev_one_bound_of_norm_le_one
    (m : E → ℂ) (hm : MemLp m ⊤) (hbound : ∀ ξ, ‖m ξ‖ ≤ 1)
    (f : L²) (hf : MemFourierSobolev 1 f) :
    MemFourierSobolev 1 (fourierMultiplier (hm.toLp m) f) ∧
      fourierSobolevNorm 1 (fourierMultiplier (hm.toLp m) f) ≤
        fourierSobolevNorm 1 f := by
  have hF : 𝓕 (fourierMultiplier (hm.toLp m) f) =
      multiplicationOperator (hm.toLp m) (𝓕 f) := by
    change (Lp.fourierTransformₗᵢ E ℂ)
      ((Lp.fourierTransformₗᵢ E ℂ).symm _) = _
    exact (Lp.fourierTransformₗᵢ E ℂ).apply_symm_apply _
  have hb : ∀ᵐ ξ ∂volume,
      ‖weightedL2Fourier 1 (fourierMultiplier (hm.toLp m) f) ξ‖ ≤
        ‖weightedL2Fourier 1 f ξ‖ := by
    filter_upwards [multiplicationOperator_coeFn (hm.toLp m) (𝓕 f),
      hm.coeFn_toLp] with ξ hξ hmξ
    simp only [norm_weightedL2Fourier, hF, hξ, hmξ, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (euclideanSobolevWeight_pos 1 ξ).le
    exact (mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _)).trans_eq
      (one_mul _)
  exact ⟨MemLp.mono hf (aestronglyMeasurable_weightedL2Fourier _ _) hb,
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_ae (aestronglyMeasurable_weightedL2Fourier _ _) hb)⟩

/-- The actual differentiated image inverse is an H¹ contraction, for
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageDerivativeBesselL2Operator_sobolev_one_bound (a : Fin d)
    (f : L²) (hf : MemFourierSobolev 1 f) :
    MemFourierSobolev 1 (imageDerivativeBesselL2Operator a f) ∧
      fourierSobolevNorm 1 (imageDerivativeBesselL2Operator a f) ≤
        fourierSobolevNorm 1 f :=
  fourierMultiplier_sobolev_one_bound_of_norm_le_one _
    (memLp_top_imageDerivativeBesselSymbol a)
    (norm_imageDerivativeBesselSymbol_le_one a) f hf

/-- The actual image inverse is an H¹ contraction, for
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem imageBesselL2Operator_sobolev_one_bound
    (f : L²) (hf : MemFourierSobolev 1 f) :
    MemFourierSobolev 1 (imageBesselL2Operator f) ∧
      fourierSobolevNorm 1 (imageBesselL2Operator f) ≤ fourierSobolevNorm 1 f := by
  apply fourierMultiplier_sobolev_one_bound_of_norm_le_one _
    memLp_top_complex_imageBesselSymbol _ f hf
  intro ξ
  rw [Complex.norm_real, Real.norm_eq_abs, imageBesselSymbol,
    abs_of_pos (euclideanSobolevWeight_pos _ _)]
  exact (euclideanSobolevWeight_mono (by norm_num : (-1 : ℝ) ≤ 0) _).trans_eq
    (euclideanSobolevWeight_zero _)

/-- A smooth compact real coefficient gives an actual H¹ multiplication bound.
The bounds on its derivatives are proved from compact support, as needed for
the masked coefficients `μ A`, `μ Z`, and `χ` in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem freezingPhysicalMultiplier_sobolev_one_bound
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L², MemFourierSobolev 1 f →
      MemFourierSobolev 1 (freezingPhysicalMultiplier χ hχ.continuous hχc f) ∧
        fourierSobolevNorm 1 (freezingPhysicalMultiplier χ hχ.continuous hχc f) ≤
          C * fourierSobolevNorm 1 f := by
  let c : E → ℂ := fun x ↦ (χ x : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hχ
  have hcs : HasCompactSupport c := hχc.comp_left Complex.ofReal_zero
  have hb (r : ℕ) : ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ r c x‖ ≤ K :=
    (hcs.iteratedFDeriv r).exists_bound_of_continuous
      (hc.continuous_iteratedFDeriv (by simp))
  choose K hK using hb
  let C : ℕ → ℝ := fun r ↦ max 0 (K r)
  have hC (r : ℕ) : 0 ≤ C r := le_max_left _ _
  refine ⟨localizedMultiplierConstant d 1 * (C 1 + C 0),
    mul_nonneg (localizedMultiplierConstant_pos d 1).le (add_nonneg (hC 1) (hC 0)), ?_⟩
  intro f hf
  have he : freezingPhysicalMultiplier χ hχ.continuous hχc f =
      localizedScalarProduct c hc hcs f := by
    apply Lp.ext
    filter_upwards [freezingPhysicalMultiplier_coeFn χ hχ.continuous hχc f,
      localizedScalarProduct_ae c hc hcs f] with x hx hy
    simp only [hx, hy, c, Complex.real_smul]
  rw [he]
  obtain ⟨hm, hn⟩ := localizedScalarProduct_frechet_bound 1 c hc hcs C hC
    (fun r _ x ↦ (hK r x).trans (le_max_right _ _)) f (by simpa only [Nat.cast_one] using hf)
  simp only [Nat.cast_one] at hm hn
  refine ⟨hm, hn.trans ?_⟩
  have hfn := norm_le_fourierSobolevNorm (by norm_num : (0 : ℝ) ≤ 1) hf
  calc
    _ = localizedMultiplierConstant d 1 *
        (C 1 * ‖f‖ + C 0 * fourierSobolevNorm 1 f) := by
      simp [mixedAmplitudeSobolevSum, Finset.sum_range_succ]
    _ ≤ localizedMultiplierConstant d 1 *
        (C 1 * fourierSobolevNorm 1 f + C 0 * fourierSobolevNorm 1 f) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hfn (hC 1)) le_rfl)
        (localizedMultiplierConstant_pos d 1).le
    _ = _ := by ring

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
