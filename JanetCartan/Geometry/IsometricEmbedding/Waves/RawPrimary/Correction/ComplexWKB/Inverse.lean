module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.WKB.Operator

/-!
# Complexification of the concrete orthogonal inverse

The restricted inverse in `app:ch_waves:eq:primary-algebraic-correction` acts
on both quadratures. These are the actual Hermitian orthogonal complements of
the real nullvectors, inside the whole complex Euclidean space. The consumer
is the identification of `fullCorrectionCovector` with `WKB.algebraicCorrection`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport

variable {n : ℕ} {H : MetricTensor n} {row col : Fin n}

/-- Complex extension of the SAME real symbol (or inverse matrix), as used in
`app:ch_waves:eq:primary-algebraic-correction`. -/
def complexSymbolMap (H : MetricTensor n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (H.map Complex.ofReal).toEuclideanLin

/-- Real quadrature of the concrete matrix extension
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexSymbolMap_re (H : MetricTensor n) (v : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    (complexSymbolMap H v i).re = (H *ᵥ fun j ↦ (v j).re) i := by
  simp [complexSymbolMap, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Complex.mul_re]

/-- Imaginary quadrature of the concrete matrix extension
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexSymbolMap_im (H : MetricTensor n) (v : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    (complexSymbolMap H v i).im = (H *ᵥ fun j ↦ (v j).im) i := by
  simp [complexSymbolMap, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Complex.mul_im]

/-- The complex extension agrees with the real inclusion on real inputs
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexSymbolMap_inclusion (H : MetricTensor n) (v : Euclidean n) :
    complexSymbolMap H (euclideanComplexInclusion v) =
      euclideanComplexInclusion (H.toEuclideanLin v) := by
  ext i
  apply Complex.ext
  · simp [complexSymbolMap_re, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  · simp [complexSymbolMap_im, Matrix.mulVec, dotProduct]

/-- The Hermitian orthogonal domain in
`app:ch_waves:eq:primary-algebraic-correction`. -/
def complexSymbolDomainPerp (H : MetricTensor n) (col : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  (ℂ ∙ euclideanComplexInclusion (WithLp.toLp 2 (rightNullvector H col)))ᗮ

/-- The Hermitian orthogonal range in
`app:ch_waves:eq:primary-algebraic-correction`. -/
def complexSymbolRangePerp (H : MetricTensor n) (row : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  (ℂ ∙ euclideanComplexInclusion (WithLp.toLp 2 (leftNullvector H row)))ᗮ

private theorem mem_complex_perp (k : Fin n → ℝ) (v : EuclideanSpace ℂ (Fin n)) :
    v ∈ (ℂ ∙ euclideanComplexInclusion (WithLp.toLp 2 k))ᗮ ↔
      k ⬝ᵥ (fun j ↦ (v j).re) = 0 ∧ k ⬝ᵥ (fun j ↦ (v j).im) = 0 := by
  simp [Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.ext_iff,
    Complex.mul_re, Complex.mul_im, mul_comm]

/-- Both quadratures must lie in `kᗮ`; neither channel is discarded
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem mem_complexSymbolDomainPerp (v : EuclideanSpace ℂ (Fin n)) :
    v ∈ complexSymbolDomainPerp H col ↔
      rightNullvector H col ⬝ᵥ (fun j ↦ (v j).re) = 0 ∧
      rightNullvector H col ⬝ᵥ (fun j ↦ (v j).im) = 0 :=
  mem_complex_perp _ _

/-- Both quadratures of the transport right-hand side lie in `lᗮ`
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem mem_complexSymbolRangePerp (v : EuclideanSpace ℂ (Fin n)) :
    v ∈ complexSymbolRangePerp H row ↔
      leftNullvector H row ⬝ᵥ (fun j ↦ (v j).re) = 0 ∧
      leftNullvector H row ⬝ᵥ (fun j ↦ (v j).im) = 0 :=
  mem_complex_perp _ _

/-- The complexified symbol maps the whole space into `lᗮ`
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexSymbolMap_mem_range (hH : H.det = 0) (v : EuclideanSpace ℂ (Fin n)) :
    complexSymbolMap H v ∈ complexSymbolRangePerp H row := by
  simp only [mem_complexSymbolRangePerp, complexSymbolMap_re, complexSymbolMap_im]
  constructor <;> rw [dotProduct_mulVec, leftNullvector_vecMul hH, zero_dotProduct]

/-- The SAME Gram inverse takes arbitrary complex inputs into `kᗮ`
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexOrthogonalSymbolInverse_mem_domain (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : EuclideanSpace ℂ (Fin n)) :
    complexSymbolMap (orthogonalSymbolInverse H col) v ∈ complexSymbolDomainPerp H col := by
  simp only [mem_complexSymbolDomainPerp, complexSymbolMap_re, complexSymbolMap_im]
  exact ⟨orthogonalSymbolInverse_orthogonal hH hm _,
    orthogonalSymbolInverse_orthogonal hH hm _⟩

/-- Left inverse on the full complex orthogonal domain, proved on both
quadratures from the real inverse (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexOrthogonalSymbolInverse_symbol (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) {v : EuclideanSpace ℂ (Fin n)}
    (hv : v ∈ complexSymbolDomainPerp H col) :
    complexSymbolMap (orthogonalSymbolInverse H col) (complexSymbolMap H v) = v := by
  obtain ⟨hr, hi⟩ := (mem_complexSymbolDomainPerp v).mp hv
  ext i
  apply Complex.ext
  · simp only [complexSymbolMap_re, orthogonalSymbolInverse_symbol hH hm hr]
  · simp only [complexSymbolMap_im, orthogonalSymbolInverse_symbol hH hm hi]

/-- Right inverse on the full complex transport-solvable range
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexSymbol_orthogonalSymbolInverse (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) {v : EuclideanSpace ℂ (Fin n)}
    (hv : v ∈ complexSymbolRangePerp H row) :
    complexSymbolMap H (complexSymbolMap (orthogonalSymbolInverse H col) v) = v := by
  obtain ⟨hr, hi⟩ := (mem_complexSymbolRangePerp v).mp hv
  ext i
  apply Complex.ext
  · simp only [complexSymbolMap_re, symbol_orthogonalSymbolInverse hH hm hr]
  · simp only [complexSymbolMap_im, symbol_orthogonalSymbolInverse hH hm hi]

/-- The actual complex orthogonal restriction is an equivalence, with the
published Gram inverse, not an assumed inverse
(`app:ch_waves:eq:primary-algebraic-correction`). -/
def complexOrthogonalSymbolEquiv (hH : H.det = 0) (hm : H.adjugate row col ≠ 0) :
    complexSymbolDomainPerp H col ≃ₗ[ℂ] complexSymbolRangePerp H row where
  toLinearMap := ((complexSymbolMap H).domRestrict (complexSymbolDomainPerp H col)).codRestrict
    (complexSymbolRangePerp H row) (fun v ↦ complexSymbolMap_mem_range hH v)
  invFun v := ⟨complexSymbolMap (orthogonalSymbolInverse H col) v,
    complexOrthogonalSymbolInverse_mem_domain hH hm v⟩
  left_inv v := Subtype.ext (complexOrthogonalSymbolInverse_symbol hH hm v.property)
  right_inv v := Subtype.ext (complexSymbol_orthogonalSymbolInverse hH hm v.property)

/-- This equivalence is the literal symbol, supplying the symbol hypothesis
of `WKB.algebraicCorrection_cancel`
(`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexOrthogonalSymbolEquiv_apply (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : complexSymbolDomainPerp H col) :
    (complexOrthogonalSymbolEquiv hH hm v : EuclideanSpace ℂ (Fin n)) =
      complexSymbolMap H v := rfl

/-- On transport-solvable inputs the concrete inverse is exactly the inverse
in the WKB correction API (`app:ch_waves:eq:primary-algebraic-correction`). -/
theorem complexOrthogonalSymbolEquiv_symm_apply (hH : H.det = 0)
    (hm : H.adjugate row col ≠ 0) (v : complexSymbolRangePerp H row) :
    ((complexOrthogonalSymbolEquiv hH hm).symm v : EuclideanSpace ℂ (Fin n)) =
      complexSymbolMap (orthogonalSymbolInverse H col) v := rfl

end JanetCartan.RawPrimary
