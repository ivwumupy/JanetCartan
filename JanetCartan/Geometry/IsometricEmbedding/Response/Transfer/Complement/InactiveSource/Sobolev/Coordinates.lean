module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# From carrier spectral energy to the actual vector Sobolev space

The coordinate and real-norm conversion for the inactive source estimate in
`app:ch_osc:prop:osc-source-shell`, consumed by `masked_carrierSource_sobolev`.
The Fourier representative is in Mathlib's unit-period frequency variable.
Weighted integrability is proved before comparing the real-valued norms.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential JanetCartan.Localization
namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ I
local notation "H" => Lp V 2 (volume : Measure E)

private theorem norm_weighted_representative_sq (s : ℝ) (G : E → V) (ξ : E) :
    ‖euclideanSobolevWeight s ξ • G ξ‖ ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ s * ‖G ξ‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (euclideanSobolevWeight_pos _ _), mul_pow]
  congr 1
  rw [euclideanSobolevWeight, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  norm_num

private theorem weighted_representative_norm (s : ℝ) (G : E → V)
    (hm : AEStronglyMeasurable G volume) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ • G ξ) 2 volume).toReal =
      fourierWeightedL2Norm volume s G := by
  have hw : AEStronglyMeasurable (fun ξ ↦ euclideanSobolevWeight s ξ • G ξ) volume :=
    (continuous_euclideanSobolevWeight s).aestronglyMeasurable.smul hm
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hw]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [fourierWeightedL2Norm, Real.sqrt_eq_rpow]
  congr 2
  funext ξ
  exact norm_weighted_representative_sq s G ξ

/-- The actual finite Hilbert coordinates inherit weighted L² membership and
a quantitative norm bound from the Fourier representative's integrable energy.
This supplies the real-norm conversion for `masked_carrierSource_sobolev` in
`app:ch_osc:prop:osc-source-shell`. The fixed dimension factor is explicit. -/
theorem vectorSobolev_of_fourier_energy (s : ℝ) (u : H) (G : E → V)
    (hm : AEStronglyMeasurable G volume) (he : (𝓕 u : H) =ᵐ[volume] G)
    (hi : Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖G ξ‖ ^ 2) volume) :
    MemVectorFourierSobolev s u ∧
      vectorFourierSobolevNorm s u ≤
        (Fintype.card I : ℝ) * fourierWeightedL2Norm volume s G := by
  have hw : MemLp (fun ξ ↦ euclideanSobolevWeight s ξ • G ξ) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm
      ((continuous_euclideanSobolevWeight s).aestronglyMeasurable.smul hm)).mpr
    change Integrable (fun ξ ↦ ‖euclideanSobolevWeight s ξ • G ξ‖ ^ 2) volume
    simpa only [norm_weighted_representative_sq] using hi
  have hb (i : I) : ∀ᵐ ξ ∂volume,
      ‖weightedL2Fourier s (finiteL2CoordinateIsometry volume u i) ξ‖ ≤
        ‖euclideanSobolevWeight s ξ • G ξ‖ := by
    have hc := finiteL2Coordinates_apply_ae volume (𝓕 u) i
    change (finiteL2CoordinateIsometry volume (𝓕 u) i : E → ℂ) =ᵐ[volume]
      (fun ξ ↦ (𝓕 u : H) ξ i) at hc
    rw [coordinate_fourier] at hc
    filter_upwards [hc, he] with ξ hξ hG
    rw [norm_weightedL2Fourier, hξ, hG, norm_smul, Real.norm_eq_abs,
      abs_of_pos (euclideanSobolevWeight_pos _ _)]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (G ξ) i)
      (euclideanSobolevWeight_pos _ _).le
  have hc (i : I) : MemFourierSobolev s (finiteL2CoordinateIsometry volume u i) :=
    hw.mono (aestronglyMeasurable_weightedL2Fourier _ _) (hb i)
  refine ⟨hc, (matrixFourierSobolevNorm_le_sum s _).trans ?_⟩
  calc
    _ ≤ ∑ _ : I, fourierWeightedL2Norm volume s G := by
      apply Finset.sum_le_sum
      intro i _
      rw [← weighted_representative_norm s G hm]
      exact ENNReal.toReal_mono hw.eLpNorm_ne_top
        (eLpNorm_mono_ae (aestronglyMeasurable_weightedL2Fourier _ _) (hb i))
    _ = _ := by simp

end JanetCartan.ResponseTransfer.Complement.InactiveSource
