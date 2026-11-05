module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
public import JanetCartan.Analysis.Microlocal.Localization.NormalizedEstimates

/-!
# Comparing physical and unit-period negative Fourier norms

The source estimate `app:ch_osc:eq:osc-source-negative` uses physical frequency,
whereas the shared L² Sobolev norm uses Mathlib's unit-period frequency. This
module supplies the quantitative conversion consumed by the local pairing in
`app:ch_regular_base:eq:negative-duality` and hence by
`app:ch_regular:eq:inverse-remainder`.

For arbitrary scalar Euclidean L² data, the unnormalized physical representative
is `(𝓕 u)((2π)⁻¹ • ξ)`. Its negative weighted energy is integrable, and the
comparison constant is exactly `(2π)^(N - n/2)`. The change of variables retains
the Jacobian `(2π)^n`. No L¹ assumption is used for these results.

For L¹ ∩ L² data the representative agrees almost everywhere with the ordinary
physical Fourier integral. In the paper's additional `(2π)^(-n)` normalization,
the comparison constant becomes `(2π)^(N + n/2)`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
namespace JanetCartan.ArbitraryAccuracy
open Pseudodifferential JanetCartan.Localization
variable {n : ℕ}

private theorem integral_norm_sq_eq (f : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

private theorem weighted_norm_sq (s : ℝ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖weightedL2Fourier s u ξ‖ ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ s * ‖(𝓕 u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) ξ‖ ^ 2 := by
  rw [norm_weightedL2Fourier, mul_pow, euclideanSobolevWeight,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The two shared weighted-norm APIs agree at the same frequency convention,
provided the weighted Fourier representative belongs to L². This is the norm
identification for `app:ch_regular_base:eq:negative-duality`. -/
theorem fourierSobolevNorm_eq_fourierWeightedL2Norm {s : ℝ}
    {u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2} (hu : MemFourierSobolev s u) :
    fourierSobolevNorm s u = fourierWeightedL2Norm volume s
      (𝓕 u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) := by
  have he : (∫ ξ, ‖weightedL2Fourier s u ξ‖ ^ 2) = ‖hu.toLp _‖ ^ 2 := by
    rw [← integral_norm_sq_eq]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with ξ hξ
    rw [hξ]
  simp_rw [weighted_norm_sq] at he
  rw [fourierWeightedL2Norm, he, Real.sqrt_sq (norm_nonneg _)]
  exact (Lp.norm_toLp _ hu).symm

/-- The unnormalized physical-frequency representative of arbitrary Euclidean
L² data, used to transfer `app:ch_osc:eq:osc-source-negative` to the shared
Sobolev scale. This definition does not require L¹ membership. -/
def physicalL2Fourier (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (𝓕 u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) ((2 * Real.pi)⁻¹ • ξ)

/-- Physical-frequency squared integrability for arbitrary L² data, needed
before using the negative norm in `app:ch_regular_base:eq:negative-duality`. -/
theorem integrable_norm_sq_physicalL2Fourier
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    Integrable (fun ξ ↦ ‖physicalL2Fourier u ξ‖ ^ 2) := by
  exact ((Lp.memLp (𝓕 u)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_smul
    (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))

/-- The exact physical-frequency Plancherel Jacobian `(2π)^n`, for the norm
conversion in `app:ch_osc:eq:osc-source-negative`. -/
theorem integral_norm_sq_physicalL2Fourier
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    (∫ ξ, ‖physicalL2Fourier u ξ‖ ^ 2) = (2 * Real.pi) ^ n * ‖u‖ ^ 2 := by
  unfold physicalL2Fourier
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun ξ : EuclideanSpace ℝ (Fin n) ↦
      ‖(𝓕 u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) ξ‖ ^ 2)
    (by positivity : 0 ≤ 2 * Real.pi),
    integral_norm_sq_eq, Lp.norm_fourier_eq]
  simp

private theorem integrable_negative_energy {H : EuclideanSpace ℝ (Fin n) → ℂ}
    (hH : Integrable (fun ξ ↦ ‖H ξ‖ ^ 2)) (N : ℕ) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) * ‖H ξ‖ ^ 2) := by
  apply hH.bdd_mul (c := 1)
  · exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ ↦ Or.inl (show (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 by positivity))).aestronglyMeasurable
  · filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])
      (by simp)

/-- Every L² datum has finite physical negative weighted energy, without an
L¹ hypothesis (`app:ch_regular_base:eq:negative-duality`). -/
theorem integrable_negative_energy_physicalL2Fourier (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) * ‖physicalL2Fourier u ξ‖ ^ 2) :=
  integrable_negative_energy (integrable_norm_sq_physicalL2Fourier u) N

private theorem negative_weight_dilation_le (N : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) ≤ (2 * Real.pi) ^ (2 * N) *
      (1 + ‖(2 * Real.pi) • ξ‖ ^ 2) ^ (-(N : ℝ)) := by
  have hc : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  have hp : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hq : 0 < 1 + ‖(2 * Real.pi) • ξ‖ ^ 2 := by positivity
  have hb : 1 + ‖(2 * Real.pi) • ξ‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  rw [Real.rpow_neg hp.le, Real.rpow_neg hq.le, Real.rpow_natCast, Real.rpow_natCast]
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (pow_pos hp _) (pow_pos hq _), one_mul]
  simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (le_of_lt hq) hb N

/-- Positivity of the comparison factor used for the unnormalized physical
negative norm in `app:ch_regular_base:eq:negative-duality`. -/
theorem physical_negative_comparison_constant_pos (n N : ℕ) :
    0 < (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) := by positivity

/-- The physical negative norm controls the shared L² Sobolev norm with the
explicit factor `(2π)^(N - n/2)`. This is the frequency-convention bridge used
by `app:ch_regular_base:eq:negative-duality` and `app:ch_regular:eq:inverse-remainder`. -/
theorem fourierSobolevNorm_negative_le_physicalL2Fourier (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    fourierSobolevNorm (-(N : ℝ)) u ≤
      (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) *
        fourierWeightedL2Norm volume (-(N : ℝ)) (physicalL2Fourier u) := by
  have hconstant : (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) =
      (2 * Real.pi) ^ N / Real.sqrt ((2 * Real.pi) ^ n) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_natCast, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (2 * Real.pi) n, ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  rw [hconstant]
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hi := integrable_negative_energy_physicalL2Fourier N u
  have hi' := hi.comp_smul hc
  have hunit := integrable_negative_energy
    ((Lp.memLp (𝓕 u)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) N
  have hcomp := integral_mono hunit (hi'.const_mul ((2 * Real.pi) ^ (2 * N)))
    (fun ξ ↦ ?_)
  · rw [integral_const_mul] at hcomp
    rw [Measure.integral_comp_smul_of_nonneg volume
      (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) * ‖physicalL2Fourier u ξ‖ ^ 2)
      (2 * Real.pi) (hR := by positivity)] at hcomp
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hcomp
    rw [fourierSobolevNorm_eq_fourierWeightedL2Norm
      (memFourierSobolev_of_nonpos (by simp) u)]
    apply (Real.sqrt_le_sqrt hcomp).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_inv,
      show (2 * Real.pi) ^ (2 * N) = ((2 * Real.pi) ^ N) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    simp only [fourierWeightedL2Norm, div_eq_mul_inv, mul_assoc]
  · dsimp only
    have he : physicalL2Fourier u ((2 * Real.pi) • ξ) = (𝓕 u) ξ := by
      simp only [physicalL2Fourier, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [he]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (negative_weight_dilation_le N ξ)
      (sq_nonneg ‖(𝓕 u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) ξ‖)

/-- Finite negative weighted energy for arbitrary L² data in the paper's
`(2π)^(-n)` normalization (`app:ch_osc:eq:osc-source-negative`). -/
theorem integrable_negative_energy_paperL2Fourier (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) *
      ‖((2 * Real.pi) ^ n)⁻¹ • physicalL2Fourier u ξ‖ ^ 2) :=
  integrable_sobolevEnergy_real_smul (integrable_negative_energy_physicalL2Fourier N u) _

/-- Positivity of the comparison factor for the paper's normalized source
estimate `app:ch_osc:eq:osc-source-negative`. -/
theorem paper_negative_comparison_constant_pos (n N : ℕ) :
    0 < (2 * Real.pi) ^ ((N : ℝ) + (n : ℝ) / 2) := by positivity

/-- The paper-normalized physical negative norm controls the shared Sobolev
norm, with factor `(2π)^(N + n/2)` (`app:ch_osc:eq:osc-source-negative`). -/
theorem fourierSobolevNorm_negative_le_paperL2Fourier (N : ℕ)
    (u : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2) :
    fourierSobolevNorm (-(N : ℝ)) u ≤
      (2 * Real.pi) ^ ((N : ℝ) + (n : ℝ) / 2) *
        fourierWeightedL2Norm volume (-(N : ℝ))
          (fun ξ ↦ ((2 * Real.pi) ^ n)⁻¹ • physicalL2Fourier u ξ) := by
  rw [fourierWeightedL2Norm_real_smul, abs_of_pos (by positivity), ← mul_assoc,
    ← Real.rpow_natCast (2 * Real.pi) n, ← Real.rpow_neg (by positivity),
    ← Real.rpow_add (by positivity)]
  convert fourierSobolevNorm_negative_le_physicalL2Fourier N u using 1
  congr 2
  ring

/-- For actual L¹ ∩ L² data, the physical representative agrees almost
everywhere with the physical Fourier integral. The identification used in
`app:ch_osc:eq:osc-source-negative` follows from the existing L² Fourier
identification and preservation of null sets under nonzero dilation. -/
theorem physicalL2Fourier_toLp_ae_physicalFourierIntegral
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    physicalL2Fourier (h₂.toLp f) =ᵐ[volume]
      (fun ξ ↦ physicalFourierIntegral volume f
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) ξ)) := by
  have he : (𝓕 (h₂.toLp f) : Lp (α := EuclideanSpace ℝ (Fin n)) ℂ 2 volume) =ᵐ[volume]
      𝓕 f :=
    (fourierTransform_coeFn_ae_integral_hilbert (h₂.toLp f)
      (hf.congr h₂.coeFn_toLp.symm)).trans
        (Filter.Eventually.of_forall (Real.fourier_congr_ae h₂.coeFn_toLp))
  have hp := (Measure.quasiMeasurePreserving_smul
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))).ae_eq_comp he
  filter_upwards [hp] with ξ hξ
  simpa only [physicalL2Fourier, physicalFourierIntegral_eq_fourier, Function.comp_def] using! hξ

/-- The physical Fourier integral of L¹ ∩ L² data has finite negative
weighted energy (`app:ch_osc:eq:osc-source-negative`). -/
theorem integrable_negative_energy_physicalFourierIntegral (N : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) *
      ‖physicalFourierIntegral volume f
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) ξ)‖ ^ 2) := by
  apply (integrable_negative_energy_physicalL2Fourier N (h₂.toLp f)).congr
  filter_upwards [physicalL2Fourier_toLp_ae_physicalFourierIntegral hf h₂] with ξ hξ
  rw [hξ]

/-- Transfer the unnormalized physical-integral source bound to the L² class
needed in `app:ch_regular:eq:inverse-remainder`; both Fourier identification
and weighted integrability are proved from the L¹ ∩ L² assumptions. -/
theorem fourierSobolevNorm_negative_le_physicalFourierIntegral (N : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    fourierSobolevNorm (-(N : ℝ)) (h₂.toLp f) ≤
      (2 * Real.pi) ^ ((N : ℝ) - (n : ℝ) / 2) *
        fourierWeightedL2Norm volume (-(N : ℝ))
          (fun ξ ↦ physicalFourierIntegral volume f
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) ξ)) := by
  apply (fourierSobolevNorm_negative_le_physicalL2Fourier N (h₂.toLp f)).trans_eq
  congr 1
  unfold fourierWeightedL2Norm
  apply congrArg Real.sqrt
  apply integral_congr_ae
  filter_upwards [physicalL2Fourier_toLp_ae_physicalFourierIntegral hf h₂] with ξ hξ
  rw [hξ]

/-- Finite negative weighted energy of the actual paper-normalized transform
(`app:ch_osc:eq:osc-source-negative`). -/
theorem integrable_negative_energy_paperFourierTransform (N : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (-(N : ℝ)) * ‖paperFourierTransform f ξ‖ ^ 2) :=
  integrable_sobolevEnergy_real_smul (integrable_negative_energy_physicalFourierIntegral N hf h₂) _

/-- Transfer the paper-normalized source estimate
`app:ch_osc:eq:osc-source-negative` to the shared L² Sobolev norm consumed by
`app:ch_regular:eq:inverse-remainder`, with factor `(2π)^(N + n/2)`. -/
theorem fourierSobolevNorm_negative_le_paperFourierTransform (N : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    fourierSobolevNorm (-(N : ℝ)) (h₂.toLp f) ≤
      (2 * Real.pi) ^ ((N : ℝ) + (n : ℝ) / 2) *
        fourierWeightedL2Norm volume (-(N : ℝ)) (paperFourierTransform f) := by
  apply (fourierSobolevNorm_negative_le_paperL2Fourier N (h₂.toLp f)).trans_eq
  congr 1
  unfold fourierWeightedL2Norm
  apply congrArg Real.sqrt
  apply integral_congr_ae
  filter_upwards [physicalL2Fourier_toLp_ae_physicalFourierIntegral hf h₂] with ξ hξ
  simp only [hξ, paperFourierTransform, finrank_euclideanSpace, Fintype.card_fin]

end JanetCartan.ArbitraryAccuracy
