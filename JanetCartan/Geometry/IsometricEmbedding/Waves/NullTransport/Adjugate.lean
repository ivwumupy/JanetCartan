module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.DeterminantDeriv.Matrix
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.RowCol

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Nullvectors from a fixed adjugate minor

The algebra in `app:ch_waves:thm:leading`. A nonzero entry of the adjugate
selects a column and row. On the characteristic set these are nonzero nullvectors,
and their outer product equals that entry times the adjugate. In particular the
factorization and the noncharacteristic transport coefficient are conclusions,
not extra hypotheses. All statements are pointwise and use the Frobenius norm.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fixed adjugate column in `app:ch_waves:thm:leading`. -/
def rightNullvector (A : Matrix ι ι ℝ) (c : ι) : ι → ℝ := fun i ↦ A.adjugate i c

/-- The fixed adjugate row in `app:ch_waves:thm:leading`. -/
def leftNullvector (A : Matrix ι ι ℝ) (r : ι) : ι → ℝ := A.adjugate r

/-- The selected column is in the right kernel on the characteristic set
(`app:ch_waves:thm:leading`). -/
theorem mulVec_rightNullvector {A : Matrix ι ι ℝ} (hA : A.det = 0) (c : ι) :
    A *ᵥ rightNullvector A c = 0 := by
  funext i
  have h := congrArg (fun B : Matrix ι ι ℝ ↦ B i c) (Matrix.mul_adjugate A)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, rightNullvector, hA] using h

/-- The selected row is in the left kernel on the characteristic set
(`app:ch_waves:thm:leading`). -/
theorem leftNullvector_vecMul {A : Matrix ι ι ℝ} (hA : A.det = 0) (r : ι) :
    leftNullvector A r ᵥ* A = 0 := by
  funext j
  have h := congrArg (fun B : Matrix ι ι ℝ ↦ B r j) (Matrix.adjugate_mul A)
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, leftNullvector, hA] using h

/-- A nonzero fixed minor gives a nonvanishing right nullvector
(`app:ch_waves:thm:leading`). -/
theorem rightNullvector_ne_zero {A : Matrix ι ι ℝ} {r c : ι}
    (hminor : A.adjugate r c ≠ 0) : rightNullvector A c ≠ 0 := by
  intro h
  exact hminor (congrFun h r)

/-- A nonzero fixed minor gives a nonvanishing left nullvector
(`app:ch_waves:thm:leading`). -/
theorem leftNullvector_ne_zero {A : Matrix ι ι ℝ} {r c : ι}
    (hminor : A.adjugate r c ≠ 0) : leftNullvector A r ≠ 0 := by
  intro h
  exact hminor (congrFun h c)

/-- The selected coordinate detects every kernel vector. The proof uses the
invertible row replacement whose determinant is the fixed minor, as needed in
`app:ch_waves:thm:leading`. -/
theorem eq_zero_of_mulVec_eq_zero_of_coordinate_eq_zero {A : Matrix ι ι ℝ}
    {r c : ι} (hminor : A.adjugate r c ≠ 0) {v : ι → ℝ}
    (hv : A *ᵥ v = 0) (hr : v r = 0) : v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (M := A.updateRow c (Pi.single r 1))
    (by rwa [← Matrix.adjugate_apply])
  rw [Matrix.updateRow_mulVec, hv]
  simp [hr]

/-- Every kernel vector is the selected adjugate column times its selected
coordinate divided by the minor (`app:ch_waves:thm:leading`). -/
theorem kernel_eq_smul_rightNullvector {A : Matrix ι ι ℝ}
    (hA : A.det = 0) {r c : ι} (hminor : A.adjugate r c ≠ 0)
    {v : ι → ℝ} (hv : A *ᵥ v = 0) :
    v = (v r / A.adjugate r c) • rightNullvector A c := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mulVec_eq_zero_of_coordinate_eq_zero hminor
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hv, mulVec_rightNullvector hA]
    simp
  · simp [rightNullvector, hminor]

/-- The rank-one adjugate factorization follows from the characteristic equation
and the fixed nonzero minor (`app:ch_waves:thm:leading`). -/
theorem minor_mul_adjugate {A : Matrix ι ι ℝ} (hA : A.det = 0)
    {r c : ι} (hminor : A.adjugate r c ≠ 0) (i j : ι) :
    A.adjugate r c * A.adjugate i j = rightNullvector A c i * leftNullvector A r j := by
  have h := congrFun (kernel_eq_smul_rightNullvector hA hminor
    (mulVec_rightNullvector hA j)) i
  change A.adjugate i j = A.adjugate r j / A.adjugate r c * A.adjugate i c at h
  dsimp [rightNullvector, leftNullvector]
  rw [h]
  field_simp

/-- Contracting the determinant differential gives the principal transport
coefficient, with its exact nonzero scalar factor (`app:ch_waves:thm:leading`). -/
theorem minor_mul_fderiv_det {A : Matrix ι ι ℝ} (hA : A.det = 0)
    {r c : ι} (hminor : A.adjugate r c ≠ 0) (C : Matrix ι ι ℝ) :
    A.adjugate r c * fderiv ℝ Matrix.det A C =
      leftNullvector A r ⬝ᵥ (C *ᵥ rightNullvector A c) := by
  rw [Matrix.fderiv_det_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, minor_mul_adjugate hA hminor]
  ring

/-- The simple-root gap implies that the time transport coefficient is nonzero
(`app:ch_waves:thm:leading`); this is not assumed separately. -/
theorem transportCoefficient_ne_zero {A : Matrix ι ι ℝ} (hA : A.det = 0)
    {r c : ι} (hminor : A.adjugate r c ≠ 0) {C : Matrix ι ι ℝ}
    (hroot : fderiv ℝ Matrix.det A C ≠ 0) :
    leftNullvector A r ⬝ᵥ (C *ᵥ rightNullvector A c) ≠ 0 := by
  rw [← minor_mul_fderiv_det hA hminor]
  exact mul_ne_zero hminor hroot

/-- The minor and simple-root lower bounds multiply to a uniform denominator
gap for the transport equation (`app:ch_waves:thm:leading`). -/
theorem transportCoefficient_gap {A : Matrix ι ι ℝ} (hA : A.det = 0)
    {r c : ι} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hminor : δ ≤ |A.adjugate r c|) {C : Matrix ι ι ℝ}
    (hroot : ε ≤ |fderiv ℝ Matrix.det A C|) :
    δ * ε ≤ |leftNullvector A r ⬝ᵥ (C *ᵥ rightNullvector A c)| := by
  have hm : A.adjugate r c ≠ 0 := abs_pos.mp (hδ.trans_le hminor)
  rw [← minor_mul_fderiv_det hA hm, abs_mul]
  exact mul_le_mul hminor hroot hε (abs_nonneg _)

/-- The reciprocal of the fixed minor is uniformly controlled on the minor
patch (`app:ch_waves:thm:leading`). -/
theorem minor_inverse_bound {A : Matrix ι ι ℝ} {r c : ι} {δ : ℝ}
    (hδ : 0 < δ) (hminor : δ ≤ |A.adjugate r c|) :
    |(A.adjugate r c)⁻¹| ≤ δ⁻¹ := by
  simpa only [abs_inv, one_div] using one_div_le_one_div_of_le hδ hminor

/-- The reciprocal time coefficient is bounded by the reciprocal product of
the two fixed gaps (`app:ch_waves:thm:leading`). -/
theorem transportCoefficient_inverse_bound {A : Matrix ι ι ℝ} (hA : A.det = 0)
    {r c : ι} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hminor : δ ≤ |A.adjugate r c|) {C : Matrix ι ι ℝ}
    (hroot : ε ≤ |fderiv ℝ Matrix.det A C|) :
    |(leftNullvector A r ⬝ᵥ (C *ᵥ rightNullvector A c))⁻¹| ≤ (δ * ε)⁻¹ := by
  simpa only [abs_inv, one_div] using one_div_le_one_div_of_le (mul_pos hδ hε)
    (transportCoefficient_gap hA hδ hε.le hminor hroot)

end JanetCartan.NullTransport
