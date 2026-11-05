module

public import JanetCartan.Analysis.PhysicalCutoff.Contraction
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# A genuine physical high-frequency tail estimate

Paper-v2 §15, Step 6: the error of the actual real Schwartz truncation gains
`R⁻ᵏ` from its vanished inner band. The right hand side is the actual physical
Bessel-weighted Fourier norm of the original field, with radian weight
`⟨2πξ⟩ᵏ`. Weighted L² membership follows from Schwartz regularity; it is not
an additional analytic premise. Quantitative source profiles and the
Sobolev-to-C¹ estimate needed by the stage remain separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalCutoff

open Pseudodifferential

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C" => EuclideanSpace ℂ (Fin N)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The exact error transform of the SAME truncated real field (§15, Step 6). -/
theorem fourier_complexify_truncate_sub (R : ℝ) (u : 𝓢(E, V)) :
    𝓕 (complexify (truncate R u - u)) = filteredFourier R u - 𝓕 (complexify u) := by
  change fourierCLM ℝ _ (SchwartzMap.postcompCLM euclideanComplexInclusion
    (truncate R u - u)) = _
  rw [map_sub, map_sub]
  change 𝓕 (complexify (truncate R u)) - 𝓕 (complexify u) = _
  rw [complexify_truncate, fourier_complexTruncate]

/-- The physical Bessel multiplier preserves Schwartz regularity
(§15, Step 6). -/
theorem hasTemperateGrowth_physicalWeight (s : ℝ) :
    (fun ξ : E ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ)).HasTemperateGrowth :=
  (hasTemperateGrowth_euclideanSobolevWeight s).comp
    (((2 * Real.pi) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)

/-- Every physical weighted Fourier norm used below is finite, produced by
regularity of the actual field rather than assumed (§15, Step 6). -/
theorem memLp_physicalWeightedFourier (s : ℝ) (u : 𝓢(E, V)) :
    MemLp (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify u) ξ) 2 volume := by
  let g : 𝓢(E, C) := SchwartzMap.smulLeftCLM C
    (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ)) (𝓕 (complexify u))
  have hg : (g : E → C) = fun ξ ↦
      euclideanSobolevWeight s ((2 * Real.pi) • ξ) • 𝓕 (complexify u) ξ :=
    SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_physicalWeight s) _
  rw [← hg]
  exact g.memLp 2 volume

private theorem pow_le_physicalWeight {R : ℝ} (hR : 0 < R)
    (k : ℕ) (ξ : E) (hξ : R ≤ ‖(2 * Real.pi) • ξ‖) :
    R ^ k ≤ euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) := by
  have hscale : (R ^ 2) ^ ((k : ℝ) / 2) = R ^ k := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    simp only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * ((k : ℝ) / 2) = k by ring, Real.rpow_natCast]
  rw [← hscale]
  exact Real.rpow_le_rpow (by positivity)
    (by nlinarith [norm_nonneg ((2 * Real.pi) • ξ)]) (by positivity)

private theorem scaled_tail_pointwise {R : ℝ} (hR : 0 < R)
    (k : ℕ) (u : 𝓢(E, V)) (ξ : E) :
    ‖R ^ k • 𝓕 (complexify (truncate R u - u)) ξ‖ ≤
      ‖euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) • 𝓕 (complexify u) ξ‖ := by
  rw [fourier_complexify_truncate_sub, sub_apply, filteredFourier_apply]
  have hsub : symbol R ξ • 𝓕 (complexify u) ξ - 𝓕 (complexify u) ξ =
      (symbol R ξ - 1) • 𝓕 (complexify u) ξ := by rw [sub_smul, one_smul]
  rw [hsub]
  by_cases hξ : ‖(2 * Real.pi) • ξ‖ ≤ R
  · rw [symbol_eq_one hR hξ, sub_self, zero_smul, smul_zero, norm_zero]
    exact norm_nonneg _
  · rw [norm_smul, norm_smul, norm_smul,
      Real.norm_of_nonneg (pow_nonneg hR.le k),
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
    have hsym : ‖symbol R ξ - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      have hm := symbol_mem_Icc R ξ
      constructor <;> linarith [hm.1, hm.2]
    calc
      R ^ k * (‖symbol R ξ - 1‖ * ‖𝓕 (complexify u) ξ‖) ≤
          R ^ k * ‖𝓕 (complexify u) ξ‖ := by
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) hsym
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_physicalWeight hR k ξ (le_of_not_ge hξ)) (norm_nonneg _)

/-- The actual cutoff error has the physical high-frequency gain. The right
side is the original field's genuine finite physical Fourier-Sobolev norm;
there is no assumed output bound (§15, Step 6). -/
theorem physicalL2Norm_truncate_sub_le {R : ℝ} (hR : 0 < R)
    (k : ℕ) (u : 𝓢(E, V)) :
    PhysicalBernstein.physicalL2Norm (truncate R u - u) ≤
      (R ^ k)⁻¹ * (eLpNorm (fun ξ ↦
        euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal := by
  let e : 𝓢(E, C) := 𝓕 (complexify (truncate R u - u))
  have hm := memLp_physicalWeightedFourier (k : ℝ) u
  have hb : ‖(R ^ k • e).toLp 2 volume‖ ≤ (eLpNorm (fun ξ ↦
      euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
    rw [SchwartzMap.norm_toLp]
    apply ENNReal.toReal_mono hm.eLpNorm_ne_top
    exact eLpNorm_mono (R ^ k • e).continuous.aestronglyMeasurable
      (scaled_tail_pointwise hR k u)
  have he : ‖(R ^ k • e).toLp 2 volume‖ =
      R ^ k * PhysicalBernstein.physicalL2Norm (truncate R u - u) := by
    change ‖SchwartzMap.toLpCLM ℝ C 2 volume (R ^ k • e)‖ = _
    rw [map_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hR.le k)]
    congr 1
    exact (SchwartzMap.norm_fourier_toL2_eq _).trans (norm_complexify_toLp _)
  rw [he] at hb
  rw [mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hR k)).2 (by simpa only [mul_comm] using hb)

/-- The actual cutoff error gains `k` derivatives in EVERY physical Bessel
order, with the weight and Fourier convention unchanged (§15, Step 6).
At `s = floor(n/2)+2`, an independent Sobolev-to-C¹ embedding turns this
into the differential tail required by the metric-error stage. -/
theorem physicalWeightedNorm_truncate_sub_le {R : ℝ} (hR : 0 < R)
    (s : ℝ) (k : ℕ) (u : 𝓢(E, V)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (truncate R u - u)) ξ) 2 volume).toReal ≤
      (R ^ k)⁻¹ * (eLpNorm (fun ξ ↦
        euclideanSobolevWeight (s + k) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal := by
  let e : 𝓢(E, C) := SchwartzMap.smulLeftCLM C
    (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ))
      (𝓕 (complexify (truncate R u - u)))
  have he_apply (ξ : E) : e ξ = euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify (truncate R u - u)) ξ :=
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_physicalWeight s) _ _
  have hb (ξ : E) : ‖R ^ k • e ξ‖ ≤
      ‖euclideanSobolevWeight (s + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ‖ := by
    calc
      ‖R ^ k • e ξ‖ = euclideanSobolevWeight s ((2 * Real.pi) • ξ) *
          ‖R ^ k • 𝓕 (complexify (truncate R u - u)) ξ‖ := by
        rw [he_apply, smul_comm, norm_smul,
          Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
      _ ≤ euclideanSobolevWeight s ((2 * Real.pi) • ξ) *
          ‖euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) •
            𝓕 (complexify u) ξ‖ :=
        mul_le_mul_of_nonneg_left (scaled_tail_pointwise hR k u ξ)
          (euclideanSobolevWeight_pos _ _).le
      _ = ‖euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
          (euclideanSobolevWeight (k : ℝ) ((2 * Real.pi) • ξ) •
            𝓕 (complexify u) ξ)‖ := by
        conv_rhs => rw [norm_smul,
          Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
      _ = _ := by rw [smul_smul, euclideanSobolevWeight_add]
  have hnorm : ‖(R ^ k • e).toLp 2 volume‖ ≤ (eLpNorm (fun ξ ↦
      euclideanSobolevWeight (s + k) ((2 * Real.pi) • ξ) •
        𝓕 (complexify u) ξ) 2 volume).toReal := by
    rw [SchwartzMap.norm_toLp]
    apply ENNReal.toReal_mono (memLp_physicalWeightedFourier (s + k) u).eLpNorm_ne_top
    exact eLpNorm_mono (R ^ k • e).continuous.aestronglyMeasurable hb
  have he : ‖(R ^ k • e).toLp 2 volume‖ = R ^ k *
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (complexify (truncate R u - u)) ξ) 2 volume).toReal := by
    change ‖SchwartzMap.toLpCLM ℝ C 2 volume (R ^ k • e)‖ = _
    rw [map_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hR.le k)]
    congr 1
    change ‖e.toLp 2 volume‖ = _
    rw [SchwartzMap.norm_toLp]
    congr 2
    exact funext he_apply
  rw [he] at hnorm
  exact (le_inv_mul_iff₀ (pow_pos hR k)).2 hnorm

end JanetCartan.PhysicalCutoff
