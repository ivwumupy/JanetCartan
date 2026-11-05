module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import JanetCartan.Geometry.IsometricEmbedding.Calculus
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Normal projection and the second fundamental form

The projection identities of Section 2 (`main:sec:geometry`) and Definition
`app:ch_waves:defn:geometry` in `paper.tex`. For an injective differential, the
induced metric is positive definite and the tangent projection has matrix
`dF γ(F)⁻¹ (dF)ᵀ`, as in `app:ch_waves:eq:ambient-normal-inverse`.

Normality and the complementary projection identities need no regularity
hypothesis. Symmetry of the second form is proved under `C²` regularity, both
at a point and on an open coordinate domain. The final contraction and
annihilation identities supply the projection algebra for normal completion;
they do not assert surjectivity of the normal map.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-! ## The differential and its Gram matrix -/

/-- Section 2 (`main:sec:geometry`): the differential in the coordinate basis. -/
theorem fderiv_eq_sum_partialDeriv {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x v : Euclidean n) :
    fderiv ℝ F x v = ∑ i, v i • partialDeriv F x i := by
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, partialDeriv] using
    (congrArg (fderiv ℝ F x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)).symm

/-- Section 2 (`main:sec:geometry`): the matrix of `dF` in Euclidean coordinates. -/
def differentialMatrix {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℝ :=
  fun a i ↦ partialDeriv F x i a

/-- Section 2 (`main:sec:geometry`): matrix multiplication represents the differential. -/
theorem differentialMatrix_mulVec {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x v : Euclidean n) :
    (differentialMatrix F x).mulVec (fun i ↦ v i) = fun a ↦ fderiv ℝ F x v a := by
  ext a
  simp [Matrix.mulVec, dotProduct, differentialMatrix, fderiv_eq_sum_partialDeriv,
    Finset.sum_apply, mul_comm]

/-- Section 2 (`main:sec:geometry`): the induced metric is the Gram matrix `(dF)ᵀ dF`. -/
theorem inducedMetric_eq_transpose_mul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    inducedMetric F x = (differentialMatrix F x)ᵀ * differentialMatrix F x := by
  ext i j
  simp [inducedMetric, Matrix.mul_apply, differentialMatrix, PiLp.inner_apply, mul_comm]

/-- Section 2 (`main:sec:geometry`): an injective differential has positive definite Gram matrix. -/
theorem inducedMetric_posDef {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (himm : Function.Injective (fderiv ℝ F x)) :
    (inducedMetric F x).PosDef := by
  rw [inducedMetric_eq_transpose_mul]
  have hJ : Function.Injective (differentialMatrix F x).mulVec := by
    intro u v huv
    have heq : fderiv ℝ F x (WithLp.toLp 2 u) = fderiv ℝ F x (WithLp.toLp 2 v) := by
      ext a
      exact congrFun ((differentialMatrix_mulVec F x (WithLp.toLp 2 u)).symm.trans
        (huv.trans (differentialMatrix_mulVec F x (WithLp.toLp 2 v)))) a
    exact congrArg WithLp.ofLp (himm heq)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self (differentialMatrix F x) hJ

/-- Section 2 (`main:sec:geometry`): normality is orthogonality to every coordinate tangent vector. -/
theorem mem_normalSpace_iff {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} {w : Euclidean N} :
    w ∈ normalSpace F x ↔ ∀ i, inner ℝ (partialDeriv F x i) w = 0 := by
  constructor
  · intro h i
    exact h _ ⟨EuclideanSpace.single i 1, rfl⟩
  · intro h v hv
    obtain ⟨u, rfl⟩ := hv
    change inner ℝ (fderiv ℝ F x u) w = 0
    simp [fderiv_eq_sum_partialDeriv, sum_inner, inner_smul_left, h]

/-! ## Tangential and normal projections -/

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the ambient tangent projection. -/
def tangentProjection {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Euclidean N →L[ℝ] Euclidean N :=
  (LinearMap.range (fderiv ℝ F x).toLinearMap).starProjection

/-- Definition `app:ch_waves:defn:geometry`: the ambient normal projection. -/
def normalProjection {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Euclidean N →L[ℝ] Euclidean N :=
  (normalSpace F x).starProjection

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the inverse-Gram formula for tangent projection. -/
theorem tangentProjection_eq_sum {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (himm : Function.Injective (fderiv ℝ F x)) (w : Euclidean N) :
    tangentProjection F x w =
      ∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j * inner ℝ (partialDeriv F x j) w) •
        partialDeriv F x i := by
  let g := inducedMetric F x
  let b : Fin n → ℝ := fun j ↦ inner ℝ (partialDeriv F x j) w
  let c : Fin n → ℝ := g⁻¹.mulVec b
  have hc : g.mulVec c = b := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (inducedMetric_posDef himm).isUnit), Matrix.one_mulVec]
  have hsum : (∑ i, ∑ j, (g⁻¹ i j * b j) • partialDeriv F x i) =
      ∑ i, c i • partialDeriv F x i := by
    simp only [c, Matrix.mulVec, dotProduct, Finset.sum_smul]
  change tangentProjection F x w = ∑ i, ∑ j, (g⁻¹ i j * b j) • partialDeriv F x i
  rw [hsum]
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨WithLp.toLp 2 c, fderiv_eq_sum_partialDeriv F x (WithLp.toLp 2 c)⟩
  · apply mem_normalSpace_iff.mpr
    intro k
    rw [inner_sub_right]
    apply sub_eq_zero.mpr
    simpa only [g, b, Matrix.mulVec, dotProduct, inner_sum, inner_smul_right,
      inducedMetric, mul_comm] using (congrFun hc k).symm

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection acts by `dF γ(F)⁻¹ (dF)ᵀ`. -/
theorem tangentProjection_eq_matrix_mulVec {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (himm : Function.Injective (fderiv ℝ F x)) (w : Euclidean N) :
    (fun a ↦ tangentProjection F x w a) =
      (differentialMatrix F x * (inducedMetric F x)⁻¹ * (differentialMatrix F x)ᵀ).mulVec
        (fun a ↦ w a) := by
  rw [tangentProjection_eq_sum himm]
  ext a
  simp only [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, differentialMatrix,
    Finset.sum_apply, PiLp.inner_apply, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the matrix of the tangent projection. -/
theorem tangentProjection_matrix {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (himm : Function.Injective (fderiv ℝ F x)) :
    (fun a b ↦ tangentProjection F x (EuclideanSpace.single b 1) a) =
      differentialMatrix F x * (inducedMetric F x)⁻¹ * (differentialMatrix F x)ᵀ := by
  ext a b
  simpa [Matrix.mulVec, dotProduct] using congrFun (tangentProjection_eq_matrix_mulVec himm
    (EuclideanSpace.single b 1)) a

/-- Definition `app:ch_waves:defn:geometry`: the normal projection is the complementary projection. -/
theorem normalProjection_eq_sub_tangentProjection {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (w : Euclidean N) :
    normalProjection F x w = w - tangentProjection F x w :=
  Submodule.starProjection_orthogonal_val _

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection fixes the differential. -/
theorem tangentProjection_fderiv {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x v : Euclidean n) : tangentProjection F x (fderiv ℝ F x v) = fderiv ℝ F x v :=
  Submodule.starProjection_eq_self_iff.mpr ⟨v, rfl⟩

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection annihilates normal vectors. -/
theorem tangentProjection_eq_zero_of_mem_normalSpace {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {w : Euclidean N}
    (hw : w ∈ normalSpace F x) : tangentProjection F x w = 0 := by
  exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hw

/-- Definition `app:ch_waves:defn:geometry`: normal projection fixes normal vectors. -/
theorem normalProjection_eq_self_of_mem_normalSpace {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {w : Euclidean N}
    (hw : w ∈ normalSpace F x) : normalProjection F x w = w :=
  Submodule.starProjection_eq_self_iff.mpr hw

/-- Definition `app:ch_waves:defn:geometry`: normal projection annihilates tangent vectors. -/
theorem normalProjection_fderiv {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x v : Euclidean n) : normalProjection F x (fderiv ℝ F x v) = 0 := by
  rw [normalProjection_eq_sub_tangentProjection, tangentProjection_fderiv, sub_self]

/-- Definition `app:ch_waves:defn:geometry`: the normal projection takes values in the normal space. -/
theorem normalProjection_mem_normalSpace {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) : normalProjection F x w ∈ normalSpace F x :=
  Subtype.coe_prop _

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection is idempotent. -/
theorem tangentProjection_idempotent {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    tangentProjection F x (tangentProjection F x w) = tangentProjection F x w :=
  Submodule.starProjection_eq_self_iff.mpr (Subtype.coe_prop _)

/-- Definition `app:ch_waves:defn:geometry`: normal projection is idempotent. -/
theorem normalProjection_idempotent {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    normalProjection F x (normalProjection F x w) = normalProjection F x w :=
  normalProjection_eq_self_of_mem_normalSpace (normalProjection_mem_normalSpace F x w)

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection annihilates normal projection. -/
theorem tangentProjection_normalProjection {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    tangentProjection F x (normalProjection F x w) = 0 :=
  tangentProjection_eq_zero_of_mem_normalSpace (normalProjection_mem_normalSpace F x w)

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: normal projection annihilates tangent projection. -/
theorem normalProjection_tangentProjection {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : Euclidean N) :
    normalProjection F x (tangentProjection F x w) = 0 := by
  rw [normalProjection_eq_sub_tangentProjection, tangentProjection_idempotent, sub_self]

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the two projections sum to the identity. -/
theorem tangentProjection_add_normalProjection {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (w : Euclidean N) :
    tangentProjection F x w + normalProjection F x w = w := by
  rw [normalProjection_eq_sub_tangentProjection, add_sub_cancel]

/-! ## The second fundamental form -/

/-- Definition `app:ch_waves:defn:geometry`: the second fundamental form is normal. -/
theorem secondFundamentalForm_mem_normalSpace {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (i j : Fin n) :
    secondFundamentalForm F x i j ∈ normalSpace F x :=
  Subtype.coe_prop _

/-- Definition `app:ch_waves:defn:geometry`: the second fundamental form is orthogonal to `dF`. -/
theorem inner_partialDeriv_secondFundamentalForm {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (i j k : Fin n) :
    inner ℝ (partialDeriv F x k) (secondFundamentalForm F x i j) = 0 :=
  mem_normalSpace_iff.mp (secondFundamentalForm_mem_normalSpace F x i j) k

/-- Definition `app:ch_waves:defn:geometry`: the second fundamental form is symmetric for a `C²` map. -/
theorem secondFundamentalForm_symm {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (hF : ContDiffAt ℝ 2 F x) (i j : Fin n) :
    secondFundamentalForm F x i j = secondFundamentalForm F x j i := by
  change (normalSpace F x).starProjection (partialDeriv (fun y ↦ partialDeriv F y j) x i) =
    (normalSpace F x).starProjection (partialDeriv (fun y ↦ partialDeriv F y i) x j)
  rw [partialDeriv_partialDeriv_comm hF]

/-- Definition `app:ch_waves:defn:geometry`: symmetry on an open `C²` coordinate domain. -/
theorem secondFundamentalForm_symm_of_contDiffOn {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ 2 F s) {x : Euclidean n} (hx : x ∈ s) (i j : Fin n) :
    secondFundamentalForm F x i j = secondFundamentalForm F x j i :=
  secondFundamentalForm_symm ((hF x hx).contDiffAt (hs.mem_nhds hx)) i j

/-- Definition `app:ch_waves:defn:geometry`: subtracting the tangent component of the coordinate Hessian. -/
theorem secondFundamentalForm_eq_sub_tangentProjection {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (i j : Fin n) :
    secondFundamentalForm F x i j = partialDeriv (fun y ↦ partialDeriv F y j) x i -
      tangentProjection F x (partialDeriv (fun y ↦ partialDeriv F y j) x i) :=
  normalProjection_eq_sub_tangentProjection F x _

/-- Definition `app:ch_waves:defn:geometry`: the explicit inverse-Gram formula for the second form. -/
theorem secondFundamentalForm_eq_sub_sum {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n} (himm : Function.Injective (fderiv ℝ F x)) (i j : Fin n) :
    secondFundamentalForm F x i j = partialDeriv (fun y ↦ partialDeriv F y j) x i -
      ∑ k, ∑ l, ((inducedMetric F x)⁻¹ k l *
        inner ℝ (partialDeriv F x l) (partialDeriv (fun y ↦ partialDeriv F y j) x i)) •
          partialDeriv F x k := by
  rw [secondFundamentalForm_eq_sub_tangentProjection, tangentProjection_eq_sum himm]

/-- Equation `main:eq:tangent-normal`: normal vectors pair with the second form as with the Hessian. -/
theorem inner_secondFundamentalForm_of_mem_normalSpace {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n} {w : Euclidean N}
    (hw : w ∈ normalSpace F x) (i j : Fin n) :
    inner ℝ w (secondFundamentalForm F x i j) =
      inner ℝ w (partialDeriv (fun y ↦ partialDeriv F y j) x i) := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨w, hw⟩ _

/-! ## Identities for normal completion -/

/-- Definition `app:ch_waves:defn:geometry`: `B_F` takes values in the normal space. -/
theorem normalMap_mem_normalSpace {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (H : MetricTensor n) : normalMap F x H ∈ normalSpace F x := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (secondFundamentalForm_mem_normalSpace F x i j)

/-- Equation `main:eq:normal-completion`: the contraction identity defining the adjoint of `B_F`. -/
theorem inner_normalMap_eq_tensorPairing {n N : ℕ} (F w : Euclidean n → Euclidean N)
    (x : Euclidean n) (H : MetricTensor n) :
    inner ℝ (w x) (normalMap F x H) = tensorPairing H (normalPairing F w x) := by
  simp [normalMap, tensorPairing, normalPairing, inner_sum, inner_smul_right]

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: tangent projection annihilates `B_F`. -/
theorem tangentProjection_normalMap {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (H : MetricTensor n) : tangentProjection F x (normalMap F x H) = 0 :=
  tangentProjection_eq_zero_of_mem_normalSpace (normalMap_mem_normalSpace F x H)

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: normal projection fixes `B_F`. -/
theorem normalProjection_normalMap {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (H : MetricTensor n) :
    normalProjection F x (normalMap F x H) = normalMap F x H :=
  normalProjection_eq_self_of_mem_normalSpace (normalMap_mem_normalSpace F x H)

/-- Equation `main:eq:normal-completion`: pairing with the second form produces a symmetric tensor. -/
theorem normalPairing_isSymm {n N : ℕ} {F : Euclidean n → Euclidean N}
    (w : Euclidean n → Euclidean N) {x : Euclidean n} (hF : ContDiffAt ℝ 2 F x) :
    (normalPairing F w x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold normalPairing
  rw [secondFundamentalForm_symm hF j i]

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the second-form pairing depends only on the normal part. -/
theorem normalPairing_normalProjection {n N : ℕ} (F w : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    normalPairing F (fun y ↦ normalProjection F y (w y)) x = normalPairing F w x := by
  ext i j
  change inner ℝ ((normalSpace F x).starProjection (w x)) (secondFundamentalForm F x i j) = _
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (secondFundamentalForm_mem_normalSpace F x i j)]
  rfl

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the extended adjoint of `B_F` vanishes on tangents. -/
theorem normalPairing_tangentProjection {n N : ℕ} (F w : Euclidean n → Euclidean N)
    (x : Euclidean n) :
    normalPairing F (fun y ↦ tangentProjection F y (w y)) x = 0 := by
  ext i j
  change inner ℝ ((LinearMap.range (fderiv ℝ F x).toLinearMap).starProjection (w x))
    (secondFundamentalForm F x i j) = 0
  rw [Submodule.inner_starProjection_left_eq_right]
  change inner ℝ (w x) (tangentProjection F x (secondFundamentalForm F x i j)) = 0
  rw [tangentProjection_eq_zero_of_mem_normalSpace (secondFundamentalForm_mem_normalSpace F x i j),
    inner_zero_right]

end JanetCartan
