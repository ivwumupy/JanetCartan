module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.RightMultiplier

/-!
# The literal image-channel Bessel symbol

The multiplier in `app:ch_background:prop:bg-frame`, Step 1. The physical
covector is `2πξ` when the shared Fourier transform uses unit frequency `ξ`.
The frequency-derivative bound below is the first decay estimate needed by the
source-square commutator. It does not assert bounds for all mixed symbol jets.
-/

@[expose] public noncomputable section
open scoped RealInnerProductSpace FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Derivative of the shared inverse Bessel weight, needed by the image
commutator in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem hasFDerivAt_inverseBesselWeight (ξ : E) : HasFDerivAt (euclideanSobolevWeight (-1))
    (-(1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2) • innerSL ℝ ξ) ξ := by
  have h := ((hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.const_add 1).rpow_const
    (p := -(1 : ℝ) / 2) (Or.inl (by positivity))
  rw [show (2 : ℕ) • innerSL ℝ ξ = (2 : ℝ) • innerSL ℝ ξ by simp only [two_smul],
    smul_smul] at h
  have he : -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 := by norm_num
  have he' : (-(1 : ℝ) / 2 * (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2)) * 2 =
      -(1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2) := by ring
  rw [he, he'] at h
  exact h
/-- The frequency derivative gains one order in the image commutator of
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem norm_fderiv_inverseBesselWeight_le (ξ : E) : ‖fderiv ℝ (euclideanSobolevWeight (-1)) ξ‖ ≤
    (1 + ‖ξ‖ ^ 2)⁻¹ := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hnorm : ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
  rw [(hasFDerivAt_inverseBesselWeight ξ).fderiv, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hpos _), innerSL_apply_norm]
  calc
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(3 : ℝ) / 2) *
        (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hpos.le _)
    _ = (1 + ‖ξ‖ ^ 2)⁻¹ := by
      rw [← Real.rpow_add hpos]
      norm_num [Real.rpow_neg_one]

/-- The image multiplier in unit-frequency coordinates; the manuscript's
physical covector is `2πξ` (`app:ch_background:defn:bg-row`). -/
def imageBesselSymbol (ξ : E) : ℝ :=
  euclideanSobolevWeight (-1) ((2 * Real.pi) • ξ)

/-- The literal image symbol is a Schwartz multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasTemperateGrowth_imageBesselSymbol :
    (imageBesselSymbol (d := d)).HasTemperateGrowth := by
  exact (hasTemperateGrowth_euclideanSobolevWeight (-1)).comp
    (((2 * Real.pi) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)

/-- The real image symbol, viewed as a complex multiplier, has temperate
 growth (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasTemperateGrowth_complex_imageBesselSymbol :
    (fun ξ : E ↦ (imageBesselSymbol ξ : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp hasTemperateGrowth_imageBesselSymbol

/-- Exact Fourier action of the image Bessel multiplier on Schwartz tests
(`app:ch_background:defn:bg-row`). -/
theorem fourier_imageBesselMultiplier (u : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (schwartzFrequencyMultiplier (fun η ↦ (imageBesselSymbol η : ℂ)) u) :
      𝓢(E, ℂ)) ξ = (imageBesselSymbol ξ : ℂ) * (𝓕 u : 𝓢(E, ℂ)) ξ :=
  fourier_schwartzFrequencyMultiplier _ hasTemperateGrowth_complex_imageBesselSymbol u ξ

/-- Squaring the two inverse multipliers gives precisely the physical
Bessel denominator in the leading image amplitude
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselSymbol_sq (ξ : E) :
    imageBesselSymbol ξ * imageBesselSymbol ξ =
      (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  unfold imageBesselSymbol
  rw [← euclideanSobolevWeight_add]
  norm_num [euclideanSobolevWeight, Real.rpow_neg_one]

/-- The inverse multiplier's frequency derivative has physical order minus
two, including the chain-rule factor `2π`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_fderiv_imageBesselSymbol_le (ξ : E) :
    ‖fderiv ℝ (imageBesselSymbol (d := d)) ξ‖ ≤
      (2 * Real.pi) * (1 + ‖(2 * Real.pi) • ξ‖ ^ 2)⁻¹ := by
  let L : E →L[ℝ] E := (2 * Real.pi) • ContinuousLinearMap.id ℝ E
  have h := (hasFDerivAt_inverseBesselWeight (L ξ)).comp ξ L.hasFDerivAt
  change ‖fderiv ℝ (fun ξ ↦ euclideanSobolevWeight (-1) (L ξ)) ξ‖ ≤ _
  dsimp only [Function.comp_def] at h
  rw [h.fderiv]
  have hL : ‖L‖ ≤ 2 * Real.pi := by
    dsimp [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)).trans_eq
      (mul_one _)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hd := norm_fderiv_inverseBesselWeight_le (L ξ)
  rw [(hasFDerivAt_inverseBesselWeight (L ξ)).fderiv] at hd
  exact (mul_le_mul hd hL (norm_nonneg _) (by positivity)).trans_eq (by
    dsimp [L]
    simp only [smul_apply, ContinuousLinearMap.id_apply, mul_comm])

end JanetCartan.ContinuumNormalReduction.ImageNormal
