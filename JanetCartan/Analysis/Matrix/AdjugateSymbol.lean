module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Normalized adjugate symbols

The algebraic normalization from `app:ch_regular_base:prop:normalization` in
`paper.tex`: for an `r × r` real principal matrix `H(ξ)`, set
`c(ξ) = ‖ξ‖ ^ (1 - r) • adjugate (H(ξ))` and
`q(ξ) = ‖ξ‖ ^ (1 - r) * det (H(ξ))`. Then `H(ξ) * c(ξ) = q(ξ) • 1`.
For a matrix pencil linear in the real covector, `c` and `q` have positive
homogeneity of degrees zero and one, respectively.

The exponent is a real subtraction, not truncated natural subtraction. The
definitions are total using `Real.rpow`; the manuscript uses them off `ξ = 0`.
The algebraic and scaling identities in fact hold at zero as well. No matrix
invertibility is required, and the empty matrix case is included.

All results apply pointwise in the spatial variable and coefficient parameters.
They impose no matrix norm, so they apply with the project's Frobenius convention.
This module does not assert the regular-chart cover or coefficient derivative
bounds from the same proposition.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {E ι : Type*} [NormedAddCommGroup E] [Fintype ι] [DecidableEq ι]

/-- The amplitude `c_a` of `app:ch_regular_base:eq:schur-principal`, using the
actual adjugate and real exponent `1 - r`. -/
def normalizedAdjugateSymbol (H : E → Matrix ι ι ℝ) (ξ : E) : Matrix ι ι ℝ :=
  ‖ξ‖ ^ (1 - (Fintype.card ι : ℝ)) • (H ξ).adjugate

/-- The scalar symbol `h_a = q_a` of `app:ch_regular_base:eq:schur-principal`,
equivalently the normalized determinant in `app:ch_regular_base:eq:initial-symbols`. -/
def normalizedDeterminantSymbol (H : E → Matrix ι ι ℝ) (ξ : E) : ℝ :=
  ‖ξ‖ ^ (1 - (Fintype.card ι : ℝ)) * (H ξ).det

/-- `app:ch_regular_base:eq:normalization-exact`: `H_a c_a = q_a I`, including
singular matrices. Linearity of the principal matrix is not needed for this identity. -/
theorem mul_normalizedAdjugateSymbol (H : E → Matrix ι ι ℝ) (ξ : E) :
    H ξ * normalizedAdjugateSymbol H ξ = normalizedDeterminantSymbol H ξ • 1 := by
  rw [normalizedAdjugateSymbol, normalizedDeterminantSymbol, Matrix.mul_smul,
    Matrix.mul_adjugate, smul_smul]

/-- The reverse product in `app:ch_regular_base:eq:normalization-exact`:
the actual adjugate also gives `c_a H_a = q_a I`. -/
theorem normalizedAdjugateSymbol_mul (H : E → Matrix ι ι ℝ) (ξ : E) :
    normalizedAdjugateSymbol H ξ * H ξ = normalizedDeterminantSymbol H ξ • 1 := by
  rw [normalizedAdjugateSymbol, normalizedDeterminantSymbol, Matrix.smul_mul,
    Matrix.adjugate_mul, smul_smul]

/-- Cancellation of the normalization exponent with the adjugate degree
in `app:ch_regular_base:prop:normalization`, for a nonempty matrix. -/
private theorem rpow_one_sub_natCast_mul_pow_pred {t : ℝ} (ht : 0 < t)
    {r : ℕ} (hr : 0 < r) : t ^ (1 - (r : ℝ)) * t ^ (r - 1) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  have hexp : 1 - (r : ℝ) + ((r - 1 : ℕ) : ℝ) = 0 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hr), Nat.cast_one]
    ring
  rw [hexp, Real.rpow_zero]

/-- Cancellation of the normalization exponent with the determinant degree
in `app:ch_regular_base:prop:normalization`. -/
private theorem rpow_one_sub_natCast_mul_pow {t : ℝ} (ht : 0 < t) (r : ℕ) :
    t ^ (1 - (r : ℝ)) * t ^ r = t := by
  rw [← Real.rpow_add_natCast (ne_of_gt ht), sub_add_cancel, Real.rpow_one]

variable [NormedSpace ℝ E]

/-- The normalized adjugate in `app:ch_regular_base:prop:normalization` has
degree-zero positive homogeneity, in particular on the punctured covector space. -/
theorem normalizedAdjugateSymbol_smul (H : E →ₗ[ℝ] Matrix ι ι ℝ)
    {t : ℝ} (ht : 0 < t) (ξ : E) :
    normalizedAdjugateSymbol H (t • ξ) = normalizedAdjugateSymbol H ξ := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    ext i
    exact isEmptyElim i
  | inr h =>
    simp only [normalizedAdjugateSymbol, map_smul, Matrix.adjugate_smul,
      norm_smul_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg ξ), smul_smul]
    rw [mul_right_comm, rpow_one_sub_natCast_mul_pow_pred ht Fintype.card_pos, one_mul]

/-- The normalized determinant `q_a` in `app:ch_regular_base:prop:normalization`
has degree-one positive homogeneity, in particular off the zero covector. -/
theorem normalizedDeterminantSymbol_smul (H : E →ₗ[ℝ] Matrix ι ι ℝ)
    {t : ℝ} (ht : 0 < t) (ξ : E) :
    normalizedDeterminantSymbol H (t • ξ) = t * normalizedDeterminantSymbol H ξ := by
  simp only [normalizedDeterminantSymbol, map_smul, Matrix.det_smul,
    norm_smul_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg ξ)]
  calc
    _ = (t ^ (1 - (Fintype.card ι : ℝ)) * t ^ Fintype.card ι) *
        (‖ξ‖ ^ (1 - (Fintype.card ι : ℝ)) * (H ξ).det) := by ring
    _ = _ := by rw [rpow_one_sub_natCast_mul_pow ht]

end JanetCartan
