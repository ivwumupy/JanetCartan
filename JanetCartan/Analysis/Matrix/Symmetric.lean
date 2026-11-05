module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Symmetric tensors with the Frobenius norm

The space `E = Sym² ℝⁿ` in Definition `app:ch_seed:defn:seed-cube` of
`paper.tex` is the symmetric submodule of `MetricTensor n`. As for the ambient
matrices, use `open scoped Matrix.Norms.Frobenius` for its inherited norm.

Coordinates are indexed by unordered pairs, including diagonal pairs. The
coordinate basis has one entry on the diagonal, or two equal off-diagonal
entries. It is a coordinate basis, with off-diagonal vectors of norm `√2`.
The dimension formula holds for every `n`, hence in particular for `n ≥ 5`
as in the manuscript.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

/-- The symmetric submodule `E` of Definition `app:ch_seed:defn:seed-cube`. -/
def symmetricTensorSubmodule (n : ℕ) : Submodule ℝ (MetricTensor n) where
  carrier := {A | A.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := Matrix.IsSymm.add
  smul_mem' c _ h := h.smul c

/-- Bundled symmetric tensors from Definition `app:ch_seed:defn:seed-cube`. -/
abbrev SymmetricTensor (n : ℕ) := ↥(symmetricTensorSubmodule n)

/-- Membership in `E` is exactly matrix symmetry (app:ch_seed:defn:seed-cube). -/
@[simp] theorem mem_symmetricTensorSubmodule {n : ℕ} (A : MetricTensor n) :
    A ∈ symmetricTensorSubmodule n ↔ A.IsSymm := Iff.rfl

/-- Every bundled tensor is symmetric (app:ch_seed:defn:seed-cube). -/
theorem SymmetricTensor.isSymm {n : ℕ} (A : SymmetricTensor n) :
    (A : MetricTensor n).IsSymm := A.property

/-- Unordered-pair coordinates for `E` in app:ch_seed:defn:seed-cube. -/
def symmetricTensorCoordinates (n : ℕ) :
    SymmetricTensor n ≃ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun A := Sym2.lift ⟨A.val, fun i j ↦ A.property.apply j i⟩
  invFun c := ⟨fun i j ↦ c s(i, j), Matrix.IsSymm.ext fun i j ↦ by rw [Sym2.eq_swap]⟩
  left_inv A := rfl
  right_inv c := by ext p; induction p using Sym2.ind with | _ i j => rfl
  map_add' A B := by ext p; induction p using Sym2.ind with | _ i j => rfl
  map_smul' c A := by ext p; induction p using Sym2.ind with | _ i j => rfl

/-- Coordinates recover matrix entries (app:ch_seed:defn:seed-cube). -/
@[simp] theorem symmetricTensorCoordinates_apply {n : ℕ} (A : SymmetricTensor n)
    (i j : Fin n) : symmetricTensorCoordinates n A s(i, j) = A.val i j := rfl

/-- Arbitrary unordered-pair coordinates give a symmetric tensor
(app:ch_seed:defn:seed-cube). -/
@[simp] theorem symmetricTensorCoordinates_symm_apply {n : ℕ}
    (c : Sym2 (Fin n) → ℝ) (i j : Fin n) :
    ((symmetricTensorCoordinates n).symm c).val i j = c s(i, j) := rfl

/-- Upper-triangular entries determine `E` (app:ch_seed:defn:seed-cube). -/
theorem SymmetricTensor.ext_upper {n : ℕ} {A B : SymmetricTensor n}
    (h : ∀ i j, i ≤ j → A.val i j = B.val i j) : A = B := by
  apply Subtype.ext
  ext i j
  rcases le_total i j with hij | hji
  · exact h i j hij
  · rw [← (SymmetricTensor.isSymm A).apply i j, ← (SymmetricTensor.isSymm B).apply i j]
    exact h j i hji

/-- Coordinate basis of `E` from app:ch_seed:defn:seed-cube, indexed by unordered
pairs. Off-diagonal basis tensors have a `1` in both symmetric positions. -/
def symmetricTensorBasis (n : ℕ) :
    Module.Basis (Sym2 (Fin n)) ℝ (SymmetricTensor n) :=
  (Pi.basisFun ℝ (Sym2 (Fin n))).map (symmetricTensorCoordinates n).symm

/-- Entries of the coordinate basis (app:ch_seed:defn:seed-cube). -/
@[simp] theorem symmetricTensorBasis_apply {n : ℕ} (p : Sym2 (Fin n)) (i j : Fin n) :
    (symmetricTensorBasis n p).val i j = if p = s(i, j) then 1 else 0 := by
  simp [symmetricTensorBasis, Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply,
    eq_comm]

/-- The basis coefficients are the tensor coordinates (app:ch_seed:defn:seed-cube). -/
@[simp] theorem symmetricTensorBasis_repr {n : ℕ} (A : SymmetricTensor n)
    (p : Sym2 (Fin n)) :
    (symmetricTensorBasis n).repr A p = symmetricTensorCoordinates n A p := by
  simp [symmetricTensorBasis, Module.Basis.map_repr, Pi.basisFun_repr]

/-- Reconstruction of `E` from its independent entries (app:ch_seed:defn:seed-cube). -/
theorem symmetricTensor_sum_coordinates {n : ℕ} (A : SymmetricTensor n) :
    ∑ p, symmetricTensorCoordinates n A p • symmetricTensorBasis n p = A := by
  simpa only [symmetricTensorBasis_repr] using (symmetricTensorBasis n).sum_repr A

/-- `dim E = n(n+1)/2`, as used in app:ch_seed:defn:seed-cube and the dimension
argument of app:ch_seed:prop:seed-gram. -/
theorem finrank_symmetricTensor (n : ℕ) :
    Module.finrank ℝ (SymmetricTensor n) = n * (n + 1) / 2 := by
  rw [Module.finrank_eq_card_basis (symmetricTensorBasis n), Sym2.card, Fintype.card_fin,
    Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- The symmetric tensor dimension is the Janet–Cartan dimension
(app:ch_seed:defn:seed-cube). -/
theorem finrank_symmetricTensor_eq_embeddingDimension (n : ℕ) :
    Module.finrank ℝ (SymmetricTensor n) = embeddingDimension n :=
  finrank_symmetricTensor n

/-- The inherited norm is precisely the Frobenius norm in
app:ch_seed:defn:seed-cube. -/
theorem SymmetricTensor.norm_eq_sqrt_sum_sq {n : ℕ} (A : SymmetricTensor n) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, (A.val i j) ^ 2) := by
  change ‖A.val‖ = _
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The Frobenius pairing of a tensor with itself is its squared norm
(app:ch_seed:defn:seed-cube). -/
theorem SymmetricTensor.tensorPairing_self {n : ℕ} (A : SymmetricTensor n) :
    tensorPairing A.val A.val = ‖A‖ ^ 2 := by
  rw [SymmetricTensor.norm_eq_sqrt_sum_sq A, Real.sq_sqrt (by positivity)]
  simp only [tensorPairing, pow_two]

end JanetCartan
