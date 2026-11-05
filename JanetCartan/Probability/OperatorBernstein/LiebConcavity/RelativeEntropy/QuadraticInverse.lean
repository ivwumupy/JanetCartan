module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational

/-!
# Joint convexity of inverse quadratic forms

Completion of a positive-definite square gives joint convexity of
`(M, v) ↦ Re (v* M⁻¹ v)`. This is the algebraic ingredient for the resolvent
proof of relative-entropy convexity, used in Minsker's Fact 5 and
`app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder
open Matrix

namespace JanetCartan.OperatorBernstein.LiebConcavity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The real inverse quadratic form for the resolvent proof of
`app:ch_waves:thm:sampling`. -/
def inverseQuadraticForm (M : Matrix d d ℂ) (v : d → ℂ) : ℝ :=
  (star v ⬝ᵥ (M⁻¹ *ᵥ v)).re

omit [DecidableEq d] in
/-- Real symmetry of the Hermitian pairing, used in the square completion for
`app:ch_waves:thm:sampling`. -/
lemma star_dotProduct_re_comm (v w : d → ℂ) : (star v ⬝ᵥ w).re = (star w ⬝ᵥ v).re := by
  have h := congrArg Complex.re (star_dotProduct v w)
  simpa [dotProduct_comm] using h

/-- A completed positive-definite square bounds every variational test vector
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma inverseQuadraticForm_upper {M : Matrix d d ℂ} (hM : M.PosDef) (v w : d → ℂ) :
    2 * (star w ⬝ᵥ v).re - (star w ⬝ᵥ (M *ᵥ w)).re ≤ inverseQuadraticForm M v := by
  have hmul : M *ᵥ (M⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).mp hM.isUnit), one_mulVec]
  have hcross : (star (M⁻¹ *ᵥ v) ⬝ᵥ (M *ᵥ w)).re = (star w ⬝ᵥ v).re := by
    have h := congrArg Complex.re (hM.isHermitian.star_dotProduct_mulVec_comm (M⁻¹ *ᵥ v) w)
    simpa [hmul] using h
  have hnonneg := (RCLike.nonneg_iff.mp
    (hM.posSemidef.dotProduct_mulVec_nonneg (w - M⁻¹ *ᵥ v))).1
  change 0 ≤ (star (w - M⁻¹ *ᵥ v) ⬝ᵥ (M *ᵥ (w - M⁻¹ *ᵥ v))).re at hnonneg
  simp only [mulVec_sub, hmul, star_sub, sub_dotProduct, dotProduct_sub,
    Complex.sub_re, hcross] at hnonneg
  rw [star_dotProduct_re_comm (M⁻¹ *ᵥ v) v] at hnonneg
  unfold inverseQuadraticForm
  linarith

/-- The inverse image of the vector attains the quadratic variational bound
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma inverseQuadraticForm_attained {M : Matrix d d ℂ} (hM : M.PosDef) (v : d → ℂ) :
    inverseQuadraticForm M v =
      2 * (star (M⁻¹ *ᵥ v) ⬝ᵥ v).re -
        (star (M⁻¹ *ᵥ v) ⬝ᵥ (M *ᵥ (M⁻¹ *ᵥ v))).re := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).mp hM.isUnit), one_mulVec]
  rw [star_dotProduct_re_comm (M⁻¹ *ᵥ v) v]
  unfold inverseQuadraticForm
  ring

/-- Joint convexity of the inverse quadratic form, including empty index types.
This supplies the convex integrands in the proof of Minsker Fact 5 used in
`app:ch_waves:thm:sampling`. -/
theorem convexOn_inverseQuadraticForm :
    ConvexOn ℝ {p : Matrix d d ℂ × (d → ℂ) | p.1.PosDef}
      (fun p => inverseQuadraticForm p.1 p.2) := by
  have hc : Convex ℝ {p : Matrix d d ℂ × (d → ℂ) | p.1.PosDef} := by
    intro p hp q hq a b ha hb hab
    exact convex_posDef hp hq ha hb hab
  refine ⟨hc, ?_⟩
  intro p hp q hq a b ha hb hab
  have hm : (a • p.1 + b • q.1).PosDef := hc hp hq ha hb hab
  let w := (a • p.1 + b • q.1)⁻¹ *ᵥ (a • p.2 + b • q.2)
  have hp' := mul_le_mul_of_nonneg_left (inverseQuadraticForm_upper hp p.2 w) ha
  have hq' := mul_le_mul_of_nonneg_left (inverseQuadraticForm_upper hq q.2 w) hb
  change inverseQuadraticForm (a • p.1 + b • q.1) (a • p.2 + b • q.2) ≤
    a * inverseQuadraticForm p.1 p.2 + b * inverseQuadraticForm q.1 q.2
  rw [inverseQuadraticForm_attained hm]
  change 2 * (star w ⬝ᵥ (a • p.2 + b • q.2)).re -
    (star w ⬝ᵥ ((a • p.1 + b • q.1) *ᵥ w)).re ≤ _
  simp only [dotProduct_add, dotProduct_smul, add_mulVec, smul_mulVec,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
  linarith

end JanetCartan.OperatorBernstein.LiebConcavity
