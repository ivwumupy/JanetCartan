module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.RadialPullback.Geometry
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Jacobian of radial collar sampling

The derivative used in `app:ch_regular_base:eq:extension-collar-l2` is a scalar
identity plus a rank-one operator. Its radial eigenvalue is `-2 ^ k`; its tangential
eigenvalue is the ratio of the sampled radius to the original radius. The
rank-one determinant identity yields the Jacobian formula in every positive
dimension, including dimension one.
-/

@[expose] public noncomputable section

open Module

private theorem det_id_add_smulRight {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] ℝ) (u : E) :
    LinearMap.det (LinearMap.id + f.smulRight u) = 1 + f u := by
  classical
  let b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  change ∑ i, f (b i) * b.repr u i = f u
  conv_rhs => rw [← b.sum_repr u, map_sum]
  simp [mul_comm]

private theorem det_smul_id_add_smulRight {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) (u : E) {s : ℝ} (hs : s ≠ 0)
    (hn : 0 < Module.finrank ℝ E) :
    LinearMap.det (s • LinearMap.id + f.smulRight u) =
      s ^ (Module.finrank ℝ E - 1) * (s + f u) := by
  have heq : s • LinearMap.id + f.smulRight u =
      s • (LinearMap.id + (s⁻¹ • f).smulRight u) := by
    ext v
    simp [smul_add, smul_smul, hs]
  rw [heq, LinearMap.det_smul, det_id_add_smulRight]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

namespace JanetCartan.BallExtension.Parameters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Parameters E)

/-- The genuine derivative of the sampling map in
`app:ch_regular_base:eq:extension-collar-l2`, expressed as a scalar identity plus
a rank-one operator. This formula holds at every point other than the center. -/
theorem hasFDerivAt_radialPoint (k : ℕ) {x : E} (hx : x ≠ p.center) :
    HasFDerivAt (p.radialPoint k)
      (((p.radius - (2 : ℝ) ^ k * (‖x - p.center‖ - p.radius)) / ‖x - p.center‖) •
        ContinuousLinearMap.id ℝ E +
      ((-(p.radius * (1 + (2 : ℝ) ^ k)) / ‖x - p.center‖ ^ 3) •
        innerSL ℝ (x - p.center)).smulRight (x - p.center)) x := by
  have hr : ‖x - p.center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const p.center
  have hn : HasFDerivAt (fun y : E ↦ ‖y - p.center‖)
      (‖x - p.center‖⁻¹ • innerSL ℝ (x - p.center)) x := by
    have h := hd.norm_sq.sqrt (pow_ne_zero 2 hr)
    simp only [Real.sqrt_sq (norm_nonneg _), ContinuousLinearMap.comp_id] at h
    convert h using 1
    · rfl
    · ext v
      simp only [id_eq, smul_apply, smul_eq_mul]
      field_simp
      ring
  have hg := ((((hasDerivAt_id ‖x - p.center‖).sub_const p.radius).const_mul
    ((2 : ℝ) ^ k)).const_sub p.radius).div (hasDerivAt_id ‖x - p.center‖) hr
  have h := ((hg.comp_hasFDerivAt x hn).smul hd).const_add p.center
  convert h using 1
  · rfl
  · congr 2
    simp only [smul_smul, id_eq, mul_one]
    congr 1
    field_simp
    ring

variable {n : ℕ} (q : Parameters (EuclideanSpace ℝ (Fin n)))

/-- The signed radial sampling Jacobian in
`app:ch_regular_base:eq:extension-collar-l2`: one radial eigenvalue `-2 ^ k` and
`n - 1` tangential eigenvalues equal to the ratio of radii. -/
theorem det_fderiv_radialPoint_radialCollar (hn : 0 < n) (k : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ q.radialCollar k) :
    (fderiv ℝ (q.radialPoint k) x).det =
      -(2 : ℝ) ^ k * ((q.radius - (2 : ℝ) ^ k * (‖x - q.center‖ - q.radius)) /
        ‖x - q.center‖) ^ (n - 1) := by
  have hx' := q.radialCollar_subset_closedRadialCollar k hx
  have hxc := q.ne_center_of_mem_closedRadialCollar hx'
  have hr : ‖x - q.center‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxc)
  have hs : (q.radius - (2 : ℝ) ^ k * (‖x - q.center‖ - q.radius)) /
      ‖x - q.center‖ ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num) (q.radialPoint_scale_ge_one_third hx'))
  rw [(q.hasFDerivAt_radialPoint k hxc).fderiv]
  change LinearMap.det (_ • LinearMap.id +
    ((_ • innerSL ℝ (x - q.center)) : _ →L[ℝ] ℝ).toLinearMap.smulRight (x - q.center)) = _
  rw [det_smul_id_add_smulRight _ _ hs (by simpa using hn)]
  simp only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe, smul_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have heq : (q.radius - (2 : ℝ) ^ k * (‖x - q.center‖ - q.radius)) / ‖x - q.center‖ +
      (-(q.radius * (1 + (2 : ℝ) ^ k)) / ‖x - q.center‖ ^ 3) * ‖x - q.center‖ ^ 2 =
      -(2 : ℝ) ^ k := by
    field_simp
    ring
  rw [heq, mul_comm]

/-- Exact absolute Jacobian for the change of variables in
`app:ch_regular_base:eq:extension-collar-l2`, valid in every positive dimension. -/
theorem abs_det_fderiv_radialPoint_radialCollar (hn : 0 < n) (k : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ q.radialCollar k) :
    |(fderiv ℝ (q.radialPoint k) x).det| =
      (2 : ℝ) ^ k * ((q.radius - (2 : ℝ) ^ k * (‖x - q.center‖ - q.radius)) /
        ‖x - q.center‖) ^ (n - 1) := by
  have hs : 0 ≤ (q.radius - (2 : ℝ) ^ k * (‖x - q.center‖ - q.radius)) /
      ‖x - q.center‖ := le_trans (by norm_num)
    (q.radialPoint_scale_ge_one_third (q.radialCollar_subset_closedRadialCollar k hx))
  rw [q.det_fderiv_radialPoint_radialCollar hn k hx, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k),
    abs_of_nonneg (pow_nonneg hs _)]

/-- The uniform lower bound for the radial sampling Jacobian used in
`app:ch_regular_base:eq:extension-collar-l2`. The tangential scale is at least
one third throughout the collar. -/
theorem radialCollar_jacobian_lower_bound (hn : 0 < n) (k : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ q.radialCollar k) :
    (2 : ℝ) ^ k / (3 : ℝ) ^ (n - 1) ≤ |(fderiv ℝ (q.radialPoint k) x).det| := by
  rw [q.abs_det_fderiv_radialPoint_radialCollar hn k hx]
  have hs := q.radialPoint_scale_ge_one_third
    (q.radialCollar_subset_closedRadialCollar k hx)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hs (n - 1)
  simpa [div_pow, div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ (2 : ℝ) ^ k)

/-- In dimension one there are no tangential factors, so the absolute Jacobian
in `app:ch_regular_base:eq:extension-collar-l2` is exactly `2 ^ k`. -/
theorem abs_det_fderiv_radialPoint_dim_one
    (q : Parameters (EuclideanSpace ℝ (Fin 1))) (k : ℕ)
    {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ q.radialCollar k) :
    |(fderiv ℝ (q.radialPoint k) x).det| = (2 : ℝ) ^ k := by
  simpa using q.abs_det_fderiv_radialPoint_radialCollar (by omega) k hx

end JanetCartan.BallExtension.Parameters
