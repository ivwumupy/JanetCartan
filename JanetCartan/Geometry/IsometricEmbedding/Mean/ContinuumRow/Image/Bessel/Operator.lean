module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Synthesis
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The real L² Bessel inverse
The constructed Fourier multiplier in `app:ch_background:defn:bg-row` is a
self-adjoint contraction on the actual real Euclidean L² output space.
-/

public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

private def besselOutput (u : OutputL2 n) : OutputL2 n :=
  (exists_periodicBessel_output u).choose

private theorem coeff_besselOutput (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (besselOutput u) =
      periodicBesselSymbol k • periodicL2FourierCoeff k u :=
  (exists_periodicBessel_output u).choose_spec k

private def besselLinear : OutputL2 n →ₗ[ℝ] OutputL2 n where
  toFun := besselOutput
  map_add' u v := by
    apply periodicBessel_coeff_ext
    intro k
    simp only [coeff_besselOutput, map_add, smul_add]
  map_smul' c u := by
    apply periodicBessel_coeff_ext
    intro k
    simp only [coeff_besselOutput, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

private def l2Analysis : OutputL2 n →ₗᵢ[ℝ] PeriodicFourierL2 n (Euclidean n) :=
  (PeriodicSobolevSpace.analysisIsometry 0).comp
    PeriodicSobolevSpace.zeroEquivL2.symm.toLinearIsometry

private theorem l2Analysis_apply (u : OutputL2 n) (k : Fin n → ℤ) :
    l2Analysis u k = periodicL2FourierCoeff k u := by
  change periodicSobolevWeight 0 k • periodicL2FourierCoeff k u = _
  simp [periodicSobolevWeight]

private theorem norm_besselOutput_le (u : OutputL2 n) : ‖besselOutput u‖ ≤ ‖u‖ := by
  rw [← l2Analysis.norm_map (besselOutput u), ← l2Analysis.norm_map u]
  apply lp.norm_mono (by norm_num)
  intro k
  rw [l2Analysis_apply, l2Analysis_apply, coeff_besselOutput, norm_smul,
    Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k)

/-- The actual real periodic Bessel inverse `⟨D⟩⁻¹` in
`app:ch_background:defn:bg-row`, constructed using the complete Fourier basis. -/
def periodicBesselInverse : OutputL2 n →L[ℝ] OutputL2 n :=
  (besselLinear (n := n)).mkContinuous 1 (fun u ↦ by
    simpa only [besselLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_besselOutput_le u)

/-- Literal Fourier multiplier identity (`app:not:fourier`). -/
theorem periodicL2FourierCoeff_besselInverse (u : OutputL2 n) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (periodicBesselInverse u) =
      periodicBesselSymbol k • periodicL2FourierCoeff k u :=
  coeff_besselOutput u k

/-- The Bessel inverse is an L² contraction (`app:ch_background:defn:bg-row`). -/
theorem norm_periodicBesselInverse_apply_le (u : OutputL2 n) :
    ‖periodicBesselInverse u‖ ≤ ‖u‖ := norm_besselOutput_le u

/-- Operator norm bound for the image channel (`app:ch_background:defn:bg-row`). -/
theorem norm_periodicBesselInverse_le : ‖periodicBesselInverse (n := n)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u ↦ by
    simpa only [one_mul] using norm_periodicBesselInverse_apply_le u)

/-- The real even Fourier symbol gives symmetry (`app:ch_background:defn:bg-row`). -/
theorem periodicBesselInverse_inner (u v : OutputL2 n) :
    ⟪periodicBesselInverse u, v⟫ = ⟪u, periodicBesselInverse v⟫ := by
  rw [← l2Analysis.inner_map_map, ← l2Analysis.inner_map_map,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [l2Analysis_apply, periodicL2FourierCoeff_besselInverse,
    real_inner_smul_left, real_inner_smul_right]

/-- Self-adjointness on the full real L² space (`app:ch_background:defn:bg-row`). -/
theorem periodicBesselInverse_isSelfAdjoint :
    IsSelfAdjoint (periodicBesselInverse (n := n)) :=
  (show (periodicBesselInverse (n := n)).toLinearMap.IsSymmetric from
    periodicBesselInverse_inner).isSelfAdjoint

/-- Adjoint identity used in image-channel assembly (`app:ch_background:defn:bg-row`). -/
theorem periodicBesselInverse_adjoint :
    (periodicBesselInverse (n := n)).adjoint = periodicBesselInverse :=
  periodicBesselInverse_isSelfAdjoint.adjoint_eq

end JanetCartan.ContinuumRow
