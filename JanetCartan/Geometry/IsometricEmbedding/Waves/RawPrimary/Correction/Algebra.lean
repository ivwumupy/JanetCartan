module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Construction
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The concrete orthogonal symbol inverse

The Gram completion in `RawPrimary.Construction` realizes the orthogonal
restricted inverse in `app:ch_waves:eq:primary-algebraic-correction`.
These identities supply the algebra needed by `fullCorrectionCovector`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.RawPrimary
open NullTransport

variable {n : ℕ} {H : MetricTensor n} {row col : Fin n}

private theorem outer_mulVec (u v : Fin n → ℝ) :
    vecMulVec u u *ᵥ v = (u ⬝ᵥ v) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_comm _ _

/-- The characteristic kernel has zero intersection with its Euclidean
orthogonal complement (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem eq_zero_of_symbol_kernel_of_orthogonal (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) {v : Fin n → ℝ}
    (hv : H *ᵥ v = 0) (hk : rightNullvector H col ⬝ᵥ v = 0) : v = 0 := by
  have he := kernel_eq_smul_rightNullvector hH hm hv
  have hkk : rightNullvector H col ⬝ᵥ rightNullvector H col ≠ 0 :=
    fun h ↦ rightNullvector_ne_zero hm (dotProduct_self_eq_zero.mp h)
  rw [he, dotProduct_smul] at hk
  have hc : v row / H.adjugate row col = 0 := (mul_eq_zero.mp hk).resolve_right hkk
  rw [he, hc, zero_smul]

/-- Quadratic form of the published completion: a sum of two squares
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem dotProduct_orthogonalSymbolCompletion (H : MetricTensor n) (col : Fin n)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (orthogonalSymbolCompletion H col *ᵥ v) =
      (H *ᵥ v) ⬝ᵥ (H *ᵥ v) + (rightNullvector H col ⬝ᵥ v) ^ 2 := by
  rw [orthogonalSymbolCompletion, add_mulVec, dotProduct_add, ← mulVec_mulVec,
    dotProduct_transpose_mulVec, outer_mulVec]
  simp only [dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm v, pow_two]

/-- The fixed nonzero minor makes the actual Gram completion invertible.
No inverse hypothesis is needed (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolCompletion_isUnit (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) : IsUnit (orthogonalSymbolCompletion H col) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (LinearMap.ker_eq_bot (f := (orthogonalSymbolCompletion H col).mulVecLin)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change orthogonalSymbolCompletion H col *ᵥ v = 0 at hv
  have he := dotProduct_orthogonalSymbolCompletion H col v
  rw [hv, dotProduct_zero] at he
  have hnonneg : 0 ≤ (H *ᵥ v) ⬝ᵥ (H *ᵥ v) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hk : rightNullvector H col ⬝ᵥ v = 0 := by nlinarith [sq_nonneg (rightNullvector H col ⬝ᵥ v)]
  have hvH : H *ᵥ v = 0 := dotProduct_self_eq_zero.mp (by nlinarith)
  exact eq_zero_of_symbol_kernel_of_orthogonal hH hm hvH hk

/-- The normal equation for the SAME total inverse formula used in
`fullCorrectionCovector` (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_normal_equation (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : Fin n → ℝ) :
    orthogonalSymbolCompletion H col *ᵥ (orthogonalSymbolInverse H col *ᵥ v) =
      H.transpose *ᵥ v := by
  have hu := (orthogonalSymbolCompletion H col).isUnit_iff_isUnit_det.mp
    (orthogonalSymbolCompletion_isUnit hH hm)
  rw [orthogonalSymbolInverse, mulVec_mulVec,
    Matrix.mul_nonsing_inv_cancel_left _ _ hu]

/-- The concrete inverse takes values in `kᗮ`, with the Euclidean dot product
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_orthogonal (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : Fin n → ℝ) :
    rightNullvector H col ⬝ᵥ (orthogonalSymbolInverse H col *ᵥ v) = 0 := by
  have he := congrArg (fun w ↦ rightNullvector H col ⬝ᵥ w)
    (orthogonalSymbolInverse_normal_equation hH hm v)
  simp only [orthogonalSymbolCompletion, add_mulVec, dotProduct_add, ← mulVec_mulVec,
    dotProduct_transpose_mulVec, mulVec_rightNullvector hH, dotProduct_zero,
    outer_mulVec, dotProduct_smul, smul_eq_mul,
    zero_add] at he
  exact (mul_eq_zero.mp he).resolve_right
    (fun h ↦ rightNullvector_ne_zero hm (dotProduct_self_eq_zero.mp h))

/-- The residual of the normal equation belongs to the left kernel
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_residual_kernel (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : Fin n → ℝ) :
    H.transpose *ᵥ (v - H *ᵥ (orthogonalSymbolInverse H col *ᵥ v)) = 0 := by
  have he := orthogonalSymbolInverse_normal_equation hH hm v
  simp only [orthogonalSymbolCompletion, add_mulVec, ← mulVec_mulVec, outer_mulVec,
    orthogonalSymbolInverse_orthogonal hH hm,
    zero_smul, add_zero] at he
  rw [mulVec_sub, he, sub_self]

/-- On `kᗮ`, the concrete inverse is a left inverse to the symbol
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_symbol (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) {v : Fin n → ℝ}
    (hv : rightNullvector H col ⬝ᵥ v = 0) :
    orthogonalSymbolInverse H col *ᵥ (H *ᵥ v) = v := by
  have hu := (orthogonalSymbolCompletion H col).isUnit_iff_isUnit_det.mp
    (orthogonalSymbolCompletion_isUnit hH hm)
  have he : H.transpose *ᵥ (H *ᵥ v) = orthogonalSymbolCompletion H col *ᵥ v := by
    simp [orthogonalSymbolCompletion, add_mulVec, ← mulVec_mulVec, outer_mulVec, hv]
  rw [orthogonalSymbolInverse, ← mulVec_mulVec, he, mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, one_mulVec]

/-- Orthogonal complement of the fixed right nullvector, in the actual
Euclidean space (`app:ch_waves:eq:primary-algebraic-correction`). -/
def symbolDomainPerp (H : MetricTensor n) (col : Fin n) : Submodule ℝ (Euclidean n) :=
  (ℝ ∙ WithLp.toLp 2 (rightNullvector H col))ᗮ

/-- Orthogonal complement of the fixed left nullvector, in the actual
Euclidean space (`app:ch_waves:eq:primary-algebraic-correction`). -/
def symbolRangePerp (H : MetricTensor n) (row : Fin n) : Submodule ℝ (Euclidean n) :=
  (ℝ ∙ WithLp.toLp 2 (leftNullvector H row))ᗮ

/-- Dot-product membership criterion for the restricted domain in
`app:ch_waves:eq:primary-algebraic-correction`. -/
theorem mem_symbolDomainPerp (v : Euclidean n) :
    v ∈ symbolDomainPerp H col ↔ rightNullvector H col ⬝ᵥ (fun i ↦ v i) = 0 := by
  simp only [symbolDomainPerp, Submodule.mem_orthogonal_singleton_iff_inner_left,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- Dot-product membership criterion for the restricted target in
`app:ch_waves:eq:primary-algebraic-correction`. -/
theorem mem_symbolRangePerp (v : Euclidean n) :
    v ∈ symbolRangePerp H row ↔ leftNullvector H row ⬝ᵥ (fun i ↦ v i) = 0 := by
  simp only [symbolRangePerp, Submodule.mem_orthogonal_singleton_iff_inner_left,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- Applying the symbol after the published inverse is exactly Euclidean
orthogonal projection onto `lᗮ` (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem symbol_orthogonalSymbolInverse_eq_starProjection (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : Euclidean n) :
    H.toEuclideanLin ((orthogonalSymbolInverse H col).toEuclideanLin v) =
      (symbolRangePerp H row).starProjection v := by
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_symbolRangePerp]
    change leftNullvector H row ⬝ᵥ (H *ᵥ _) = 0
    rw [dotProduct_mulVec, leftNullvector_vecMul hH, zero_dotProduct]
  · rw [symbolRangePerp, Submodule.orthogonal_orthogonal]
    have hmT : H.transpose.adjugate col row ≠ 0 := by
      simpa only [← Matrix.adjugate_transpose, transpose_apply] using hm
    have he := kernel_eq_smul_rightNullvector (by simpa using hH) hmT
      (orthogonalSymbolInverse_residual_kernel hH hm (fun i ↦ v i))
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(v col - (H *ᵥ (orthogonalSymbolInverse H col *ᵥ v.ofLp)) col) /
      H.adjugate row col, ?_⟩
    apply PiLp.ext
    intro i
    simpa only [rightNullvector, leftNullvector, ← Matrix.adjugate_transpose,
      transpose_apply, Pi.smul_apply, Pi.sub_apply, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.toLp_apply]
      using (congrFun he i).symm

/-- Transport-solvable right-hand sides are recovered exactly by the
published inverse (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem symbol_orthogonalSymbolInverse (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) {v : Fin n → ℝ}
    (hv : leftNullvector H row ⬝ᵥ v = 0) :
    H *ᵥ (orthogonalSymbolInverse H col *ᵥ v) = v := by
  have he := symbol_orthogonalSymbolInverse_eq_starProjection hH hm (WithLp.toLp 2 v)
  rw [Submodule.starProjection_eq_self_iff.mpr ((mem_symbolRangePerp _).mpr hv)] at he
  exact congrArg WithLp.ofLp he

/-- The symbol restricted to the two Euclidean orthogonal complements is an
equivalence. Its inverse is the published Gram formula
(`app:ch_waves:eq:primary-algebraic-correction`). -/
def orthogonalSymbolEquiv (hH : H.det = 0) (hm : H.adjugate row col ≠ 0) :
    symbolDomainPerp H col ≃ₗ[ℝ] symbolRangePerp H row where
  toLinearMap := (H.toEuclideanLin.domRestrict (symbolDomainPerp H col)).codRestrict
    (symbolRangePerp H row) (fun v ↦ by
      rw [mem_symbolRangePerp]
      change leftNullvector H row ⬝ᵥ (H *ᵥ _) = 0
      rw [dotProduct_mulVec, leftNullvector_vecMul hH, zero_dotProduct])
  invFun v := ⟨(orthogonalSymbolInverse H col).toEuclideanLin v,
    (mem_symbolDomainPerp _).mpr (orthogonalSymbolInverse_orthogonal hH hm _)⟩
  left_inv v := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact orthogonalSymbolInverse_symbol hH hm ((mem_symbolDomainPerp _).mp v.property)
  right_inv v := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact symbol_orthogonalSymbolInverse hH hm ((mem_symbolRangePerp _).mp v.property)

/-- The restricted equivalence acts by the original symbol, as required for
the WKB inverse interface (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolEquiv_apply (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : symbolDomainPerp H col) :
    (orthogonalSymbolEquiv hH hm v : Euclidean n) = H.toEuclideanLin v := rfl

/-- Identification of the SAME inverse used by `fullCorrectionCovector` with
`(H|kᗮ→lᗮ)⁻¹ Π_lᗮ` (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem orthogonalSymbolInverse_eq_equiv_symm_projection (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : Euclidean n) :
    (orthogonalSymbolInverse H col).toEuclideanLin v =
      ((orthogonalSymbolEquiv hH hm).symm
        ((symbolRangePerp H row).orthogonalProjectionOnto v) : Euclidean n) := by
  let u : symbolDomainPerp H col :=
    ⟨(orthogonalSymbolInverse H col).toEuclideanLin v,
      (mem_symbolDomainPerp _).mpr (orthogonalSymbolInverse_orthogonal hH hm _)⟩
  have he : orthogonalSymbolEquiv hH hm u =
      (symbolRangePerp H row).orthogonalProjectionOnto v := by
    apply Subtype.ext
    exact symbol_orthogonalSymbolInverse_eq_starProjection hH hm v
  exact congrArg (fun w : symbolDomainPerp H col ↦ (w : Euclidean n))
    ((orthogonalSymbolEquiv hH hm).eq_symm_apply.mpr he)

end JanetCartan.RawPrimary
