module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives.Basic

/-!
# Comparison of physical and Euclidean Fourier Sobolev weights

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
the full physical derivative weight and the standard Euclidean Bessel weight
are comparable with constants `1` and `(2π)^s`. Literal measure preservation
transfers this comparison to the carrier L² classes.

The membership and norm comparisons are conditional on the explicit Fourier
transport identity `hF`. Its producer is the separate fleet task
`jc-carrier-mixed-fourier-transport`. The parent mixed-derivative construction
must instantiate this premise; no Fourier transport theorem is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

variable {n : ℕ}

/-- The standard weight is bounded by the full physical derivative weight,
for the mixed-derivative comparison in `app:ch_background:prop:bg-adjoint`. -/
theorem euclideanSobolevWeight_flatInitialCoordinates_le (s : ℕ) (ξ : CarrierVariable n) :
    euclideanSobolevWeight (s : ℝ) (flatInitialCoordinates n ξ) ≤ initialWeight s ξ := by
  unfold euclideanSobolevWeight initialWeight
  rw [flatInitialCoordinates_norm]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  have hc : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [sq_nonneg ‖initialCoordinates n ξ‖]

/-- The full physical weight costs at most `(2π)^s` compared with the standard
weight, for `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`. -/
theorem initialWeight_le_mul_euclideanSobolevWeight (s : ℕ) (ξ : CarrierVariable n) :
    initialWeight s ξ ≤ (2 * Real.pi) ^ s *
      euclideanSobolevWeight (s : ℝ) (flatInitialCoordinates n ξ) := by
  unfold euclideanSobolevWeight initialWeight
  rw [flatInitialCoordinates_norm]
  have hc : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  calc
    _ ≤ ((2 * Real.pi) ^ 2 * (1 + ‖initialCoordinates n ξ‖ ^ 2)) ^ ((s : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast_mul (by positivity)]
      congr 1
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * ((s : ℝ) / 2) = s by ring, Real.rpow_natCast]

/-- Pullback of the weighted Fourier representative to the literal carrier
measure, conditional on Fourier transport, for `app:ch_background:prop:bg-adjoint`. -/
theorem weightedL2Fourier_comp_flatInitialCoordinates_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f)) :
    weightedL2Fourier (s : ℝ) (flatInitialL2Equiv n f) ∘ flatInitialCoordinates n
      =ᵐ[carrierMeasure n]
        fun ξ => euclideanSobolevWeight (s : ℝ) (flatInitialCoordinates n ξ) •
          initialFourier n f ξ := by
  have h := flatInitialL2Equiv_symm_coeFn n (𝓕 (flatInitialL2Equiv n f))
  rw [← hF, LinearIsometryEquiv.symm_apply_apply] at h
  filter_upwards [h] with ξ hξ
  simp only [Function.comp_apply, weightedL2Fourier]
  rw [hξ, hF]
  rfl

private def standardWeightedInitialFourier (s : ℕ) (f : CarrierL2 n)
    (ξ : CarrierVariable n) : ℂ :=
  euclideanSobolevWeight (s : ℝ) (flatInitialCoordinates n ξ) • initialFourier n f ξ

private theorem aestronglyMeasurable_standardWeightedInitialFourier
    (s : ℕ) (f : CarrierL2 n) :
    AEStronglyMeasurable (standardWeightedInitialFourier s f) (carrierMeasure n) :=
  ((continuous_euclideanSobolevWeight (s : ℝ)).measurable.comp
    (flatInitialCoordinates n).measurable).aestronglyMeasurable.smul
      (Lp.memLp _).aestronglyMeasurable

private theorem memFourierSobolev_iff_memLp_standard_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f)) :
    MemFourierSobolev (s : ℝ) (flatInitialL2Equiv n f) ↔
      MemLp (standardWeightedInitialFourier s f) 2 (carrierMeasure n) := by
  have hm := (flatInitialCoordinates n).memLp_map_measure_iff
    (g := weightedL2Fourier (s : ℝ) (flatInitialL2Equiv n f))
    (p := 2) (μ := carrierMeasure n)
  rw [(flatInitialCoordinates_measurePreserving n).map_eq] at hm
  exact hm.trans (memLp_congr_ae
    (weightedL2Fourier_comp_flatInitialCoordinates_of_fourierTransport s f hF))

private theorem eLpNorm_standard_eq_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f)) :
    eLpNorm (standardWeightedInitialFourier s f) 2 (carrierMeasure n) =
      eLpNorm (weightedL2Fourier (s : ℝ) (flatInitialL2Equiv n f)) 2 volume := by
  unfold standardWeightedInitialFourier
  rw [← eLpNorm_congr_ae
    (weightedL2Fourier_comp_flatInitialCoordinates_of_fourierTransport s f hF)]
  exact eLpNorm_comp_measurePreserving (aestronglyMeasurable_weightedL2Fourier _ _)
    (flatInitialCoordinates_measurePreserving n)

private theorem norm_standard_le_physical (s : ℕ) (f : CarrierL2 n) (ξ : CarrierVariable n) :
    ‖standardWeightedInitialFourier s f ξ‖ ≤ ‖initialWeight s ξ • initialFourier n f ξ‖ := by
  simp only [standardWeightedInitialFourier, norm_smul, Real.norm_eq_abs,
    abs_of_pos (euclideanSobolevWeight_pos _ _), abs_of_pos (initialWeight_pos _ _)]
  exact mul_le_mul_of_nonneg_right (euclideanSobolevWeight_flatInitialCoordinates_le s ξ)
    (norm_nonneg _)

private theorem norm_physical_le_mul_standard (s : ℕ) (f : CarrierL2 n)
    (ξ : CarrierVariable n) :
    ‖initialWeight s ξ • initialFourier n f ξ‖ ≤
      (2 * Real.pi) ^ s * ‖standardWeightedInitialFourier s f ξ‖ := by
  simp only [standardWeightedInitialFourier, norm_smul, Real.norm_eq_abs,
    abs_of_pos (euclideanSobolevWeight_pos _ _), abs_of_pos (initialWeight_pos _ _)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (initialWeight_le_mul_euclideanSobolevWeight s ξ) (norm_nonneg (initialFourier n f ξ))

/-- Physical finite energy is equivalent to standard Euclidean Sobolev membership
under Fourier transport. This is the remaining membership input to the parent's
mixed weak derivative characterization for `app:ch_background:prop:bg-adjoint`. -/
theorem memPhysicalSobolev_iff_memFourierSobolev_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f)) :
    MemPhysicalSobolev s f ↔ MemFourierSobolev (s : ℝ) (flatInitialL2Equiv n f) := by
  rw [memFourierSobolev_iff_memLp_standard_of_fourierTransport s f hF]
  constructor
  · intro hf
    exact MemLp.mono hf (aestronglyMeasurable_standardWeightedInitialFourier s f)
      (Filter.Eventually.of_forall (norm_standard_le_physical s f))
  · intro hf
    exact hf.of_le_mul (aestronglyMeasurable_weightedInitialFourier s f)
      (Filter.Eventually.of_forall (norm_physical_le_mul_standard s f))

/-- The standard Euclidean Sobolev norm is at most the full physical energy,
under Fourier transport and finite energy, for `app:ch_background:prop:bg-adjoint`. -/
theorem fourierSobolevNorm_le_physicalSobolevNorm_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f))
    (hf : MemPhysicalSobolev s f) :
    fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) ≤ physicalSobolevNorm s f := by
  unfold fourierSobolevNorm physicalSobolevNorm
  rw [← eLpNorm_standard_eq_of_fourierTransport s f hF]
  apply ENNReal.toReal_mono hf.eLpNorm_ne_top
  exact eLpNorm_mono (aestronglyMeasurable_standardWeightedInitialFourier s f)
    (norm_standard_le_physical s f)

/-- The physical energy is at most `(2π)^s` times the standard Euclidean norm,
under Fourier transport and finite energy. This supplies the parent's mixed
norm comparison for `app:ch_background:prop:bg-inverse`. -/
theorem physicalSobolevNorm_le_mul_fourierSobolevNorm_of_fourierTransport
    (s : ℕ) (f : CarrierL2 n)
    (hF : flatInitialL2Equiv n (initialFourier n f) = 𝓕 (flatInitialL2Equiv n f))
    (hf : MemPhysicalSobolev s f) :
    physicalSobolevNorm s f ≤
      (2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) := by
  have he := (memPhysicalSobolev_iff_memFourierSobolev_of_fourierTransport s f hF).mp hf
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (aestronglyMeasurable_weightedInitialFourier s f)
    (Filter.Eventually.of_forall (norm_physical_le_mul_standard s f)) 2
  rw [eLpNorm_standard_eq_of_fourierTransport s f hF] at h
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he.eLpNorm_ne_top) h
  simpa only [physicalSobolevNorm, fourierSobolevNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2 * Real.pi) ^ s)] using hr

end JanetCartan.CarrierSobolev
