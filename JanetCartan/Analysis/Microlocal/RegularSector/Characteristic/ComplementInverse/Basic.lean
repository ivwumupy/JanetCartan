module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The characteristic complement inverse

The finite-dimensional construction in `paper-v2.tex`,
`app:ch_regular_base:eq:complement-inverse` and
`app:ch_regular_base:eq:complement-symbol`. Write `u = A k`, `q = lᵀ A`.
The rank-one completion
`C(e) = H + e A + (1-e) u q` has `lᵀ C(e) = q` and, when `H k = 0`,
`C(e) k = u`. Its restriction to `ker q` is the original pencil.
The inverse below is `C(e)⁻¹ (I-u lᵀ)`, so neither the singular full
matrix nor an orthogonal projection is substituted for the paper's objects.

Consumers: the correction amplitude `W₁` and the symbol `b₋₁ α` in
`app:ch_regular_base:lem:characteristic-kernel`. Smoothness, the interval,
and actual minor normalization are supplied by the sibling modules.
-/

open scoped Matrix Matrix.Norms.Frobenius
open Matrix
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The projection onto `ker lᵀ` along `A k` in
`app:ch_regular_base:eq:complement-inverse`. -/
def complementProjection (A : Matrix ι ι ℝ) (k l : ι → ℝ) : Matrix ι ι ℝ :=
  1 - vecMulVec (A *ᵥ k) l

/-- An explicit rank-one completion of the original pencil, used only to
construct its restricted inverse (`app:ch_regular_base:eq:complement-inverse`). -/
def pencilCompletion (H A : Matrix ι ι ℝ) (k l : ι → ℝ) (e : ℝ) :
    Matrix ι ι ℝ := H + e • A + (1 - e) • vecMulVec (A *ᵥ k) (l ᵥ* A)

/-- The actual complement inverse in `app:ch_regular_base:eq:complement-inverse`.
Its identities hold wherever the completion has nonzero determinant. -/
def complementInverse (H A : Matrix ι ι ℝ) (k l : ι → ℝ) (e : ℝ) :
    Matrix ι ι ℝ := (pencilCompletion H A k l e)⁻¹ * complementProjection A k l

omit [DecidableEq ι] in
/-- The completion carries the original left constraint to itself; this is the
completed version of `new:eq:left-null`. -/
theorem left_pencilCompletion {H A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1) (e : ℝ) :
    l ᵥ* pencilCompletion H A k l e = l ᵥ* A := by
  simp only [pencilCompletion, vecMul_add, vecMul_smul, vecMul_vecMulVec, hl, hn,
    one_smul, zero_add]
  rw [← add_smul]
  simp

/-- The oblique projection has image in `ker lᵀ`
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem left_complementProjection {A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hn : l ⬝ᵥ (A *ᵥ k) = 1) : l ᵥ* complementProjection A k l = 0 := by
  simp [complementProjection, vecMul_sub, vecMul_vecMulVec, hn]

/-- The completion is nonsingular at the root, proved from the original
one-dimensional kernel and transport normalization
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem pencilCompletion_det_ne_zero {H A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1)
    (hker : ∀ v, H *ᵥ v = 0 → ∃ c : ℝ, v = c • k) :
    (pencilCompletion H A k l 0).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  suffices hz : ∀ v, pencilCompletion H A k l 0 *ᵥ v = 0 → v = 0 by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hz
    simp [mulVec_sub, hvw]
  intro v hv
  have hq : (l ᵥ* A) ⬝ᵥ v = 0 := by
    rw [← left_pencilCompletion hl hn 0, ← dotProduct_mulVec, hv, dotProduct_zero]
  have hHv : H *ᵥ v = 0 := by
    simpa [pencilCompletion, add_mulVec, vecMulVec_mulVec, hq] using hv
  obtain ⟨c, rfl⟩ := hker v hHv
  have hc : c = 0 := by
    simpa [dotProduct_smul, ← dotProduct_mulVec, hn] using hq
  simp [hc]

/-- The constructed inverse takes values in `ker(lᵀ A)`
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem complementInverse_constraint {H A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1) {e : ℝ}
    (hd : (pencilCompletion H A k l e).det ≠ 0) :
    (l ᵥ* A) ᵥ* complementInverse H A k l e = 0 := by
  rw [← left_pencilCompletion hl hn e, vecMul_vecMul, complementInverse,
    mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hd)]
  exact left_complementProjection hn

/-- Exact multiplication by the original pencil gives the oblique projection
(`app:ch_regular_base:eq:complement-symbol`). -/
theorem complementInverse_identity {H A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1) {e : ℝ}
    (hd : (pencilCompletion H A k l e).det ≠ 0) :
    (H + e • A) * complementInverse H A k l e = complementProjection A k l := by
  have hh : pencilCompletion H A k l e * complementInverse H A k l e =
      complementProjection A k l :=
    mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hd)
  simpa only [pencilCompletion, add_mul, smul_mul, vecMulVec_mul,
    complementInverse_constraint hl hn hd, vecMulVec_zero, smul_zero, add_zero] using hh

/-- The two paper identities uniquely determine the complement inverse
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem complementInverse_unique {H A : Matrix ι ι ℝ} {k l : ι → ℝ} {e : ℝ}
    (hd : (pencilCompletion H A k l e).det ≠ 0) {b : Matrix ι ι ℝ}
    (hb : (H + e • A) * b = complementProjection A k l)
    (hq : (l ᵥ* A) ᵥ* b = 0) : b = complementInverse H A k l e := by
  have hh : pencilCompletion H A k l e * b = complementProjection A k l := by
    simp [pencilCompletion, add_mul, vecMulVec_mul, hq, hb]
  rw [complementInverse, ← hh, nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hd)]
end JanetCartan.RegularSector.Characteristic
