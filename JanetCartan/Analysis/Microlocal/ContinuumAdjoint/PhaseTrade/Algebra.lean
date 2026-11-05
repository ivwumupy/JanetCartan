module

public import JanetCartan.Analysis.Matrix.InverseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# The rectangular Gram left inverse

The algebraic part of `app:ch_background:eq:bg-derivative-trade`. The physical
matrix has `n` rows and `n - 1` columns. Its quantitative transverse gap is an
input from the Hamilton chart construction, not an assumed inverse identity.
-/

@[expose] public noncomputable section

open Matrix Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint

variable {n : ℕ}

/-- The rectangular physical/covector matrix in
`app:ch_background:eq:bg-derivative-trade`. -/
abbrev TransverseMatrix (n : ℕ) := Matrix (Fin n) (Fin (n - 1)) ℝ

/-- The squared transverse rank gap in
`app:ch_background:eq:bg-derivative-trade`. -/
def TransverseGap (δ : ℝ) (A : TransverseMatrix n) : Prop :=
  ∀ v : Fin (n - 1) → ℝ, δ * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)

/-- The literal Gram matrix in `app:ch_background:eq:bg-derivative-trade`. -/
def transverseGram (A : TransverseMatrix n) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  Aᵀ * A

/-- The literal left inverse `(Aᵀ A)⁻¹ Aᵀ` in
`app:ch_background:eq:bg-derivative-trade`. -/
def transverseLeftInverse (A : TransverseMatrix n) : Matrix (Fin (n - 1)) (Fin n) ℝ :=
  (transverseGram A)⁻¹ * Aᵀ

/-- The transverse rank gap makes the actual Gram matrix positive definite
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem transverseGram_posDef {A : TransverseMatrix n} {δ : ℝ}
    (hδ : 0 < δ) (hA : TransverseGap δ A) : (transverseGram A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa [transverseGram] using Matrix.isHermitian_conjTranspose_mul_self A
  · intro v hv
    have hp : 0 < v ⬝ᵥ v := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i))
      (Ne.symm (fun h ↦ hv (dotProduct_self_eq_zero.mp h)))
    have hg := (mul_pos hδ hp).trans_le (hA v)
    simpa [transverseGram, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.vecMul_transpose] using hg

/-- Invertibility is deduced from the transverse gap, for
`app:ch_background:eq:bg-derivative-trade`. -/
theorem isUnit_transverseGram {A : TransverseMatrix n} {δ : ℝ}
    (hδ : 0 < δ) (hA : TransverseGap δ A) : IsUnit (transverseGram A) :=
  (transverseGram_posDef hδ hA).isUnit

/-- The actual rectangular left-inverse identity in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseLeftInverse_mul {A : TransverseMatrix n} {δ : ℝ}
    (hδ : 0 < δ) (hA : TransverseGap δ A) : transverseLeftInverse A * A = 1 := by
  rw [transverseLeftInverse, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transverseGram hδ hA))

/-- Recovery of the transverse covector in
`app:ch_background:eq:bg-derivative-trade`. -/
theorem transverseLeftInverse_mulVec {A : TransverseMatrix n} {δ : ℝ}
    (hδ : 0 < δ) (hA : TransverseGap δ A) (v : Fin (n - 1) → ℝ) :
    transverseLeftInverse A *ᵥ (A *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, transverseLeftInverse_mul hδ hA, Matrix.one_mulVec]

end JanetCartan.ContinuumAdjoint
