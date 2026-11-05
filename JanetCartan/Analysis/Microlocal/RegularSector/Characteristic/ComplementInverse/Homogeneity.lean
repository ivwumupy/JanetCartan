module
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Basic
/-!
# Homogeneity of the original complement inverse

The degree-minus-one identity in `app:ch_regular_base:eq:complement-inverse`
is a consequence of uniqueness for the same pencil. The scaled completion's
nonsingularity is proved using a constructed right inverse, not assumed.
-/

open scoped Matrix Matrix.Norms.Frobenius
open Matrix
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The exact left-null identity `new:eq:left-null`, off the root. -/
theorem left_pencil {H A : Matrix ι ι ℝ} {l : ι → ℝ}
    (hl : l ᵥ* H = 0) (e : ℝ) : l ᵥ* (H + e • A) = e • (l ᵥ* A) := by
  simp [vecMul_add, vecMul_smul, hl]

omit [DecidableEq ι] in
/-- The completion fixes the missing kernel direction
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem pencilCompletion_mulVec {H A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hk : H *ᵥ k = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1) (e : ℝ) :
    pencilCompletion H A k l e *ᵥ k = A *ᵥ k := by
  have hn' : (l ᵥ* A) ⬝ᵥ k = 1 := by rwa [← dotProduct_mulVec]
  simp only [pencilCompletion, add_mulVec, smul_mulVec, vecMulVec_mulVec, hn', hk,
    MulOpposite.op_one, one_smul, zero_add]
  rw [← add_smul]
  simp

/-- The projection in `app:ch_regular_base:eq:complement-inverse` is idempotent. -/
theorem complementProjection_idempotent {A : Matrix ι ι ℝ} {k l : ι → ℝ}
    (hn : l ⬝ᵥ (A *ᵥ k) = 1) :
    complementProjection A k l * complementProjection A k l = complementProjection A k l := by
  simp [complementProjection, sub_mul, mul_sub, vecMulVec_mul_vecMulVec, hn]

/-- A restricted inverse and the original normalized kernel direction explicitly
give a right inverse of the completion
(`app:ch_regular_base:eq:complement-inverse`). -/
theorem completion_det_ne_zero_of_solution {H A : Matrix ι ι ℝ} {k l : ι → ℝ} {e : ℝ}
    (hk : H *ᵥ k = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1) {b : Matrix ι ι ℝ}
    (hb : (H + e • A) * b = complementProjection A k l)
    (hq : (l ᵥ* A) ᵥ* b = 0) : (pencilCompletion H A k l e).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_right_inverse (B := b + vecMulVec k l)
  rw [mul_add, mul_vecMulVec, pencilCompletion_mulVec hk hn]
  have hh : pencilCompletion H A k l e * b = complementProjection A k l := by
    simp [pencilCompletion, add_mul, vecMulVec_mul, hq, hb]
  rw [hh, complementProjection, sub_add_cancel]

/-- Degree-minus-one scaling for the original homogeneous pencil
(`app:ch_regular_base:eq:complement-inverse`). Both nonsingularity at the
scaled point and the inverse scaling identity are conclusions. -/
theorem complementInverse_smul {H A : Matrix ι ι ℝ} {k l : ι → ℝ} {e r : ℝ}
    (hk : H *ᵥ k = 0) (hl : l ᵥ* H = 0) (hn : l ⬝ᵥ (A *ᵥ k) = 1)
    (hd : (pencilCompletion H A k l e).det ≠ 0) (hr : r ≠ 0) :
    (pencilCompletion (r • H) A k l (r * e)).det ≠ 0 ∧
      complementInverse (r • H) A k l (r * e) = r⁻¹ • complementInverse H A k l e := by
  have hq : (l ᵥ* A) ᵥ* (r⁻¹ • complementInverse H A k l e) = 0 := by
    rw [vecMul_smul, complementInverse_constraint hl hn hd, smul_zero]
  have hb : (r • H + (r * e) • A) * (r⁻¹ • complementInverse H A k l e) =
      complementProjection A k l := by
    rw [mul_smul, ← smul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hr,
      one_smul, complementInverse_identity hl hn hd]
  have hk' : (r • H) *ᵥ k = 0 := by rw [smul_mulVec, hk, smul_zero]
  have hd' := completion_det_ne_zero_of_solution hk' hn hb hq
  exact ⟨hd', (complementInverse_unique hd' hb hq).symm⟩
end JanetCartan.RegularSector.Characteristic
