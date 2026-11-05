module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.QuadraticInverse

/-!
# The relative-entropy resolvent integrand

For positive-definite `X,A`, the matrix below represents `Z ↦ A*Z + t•(Z*X)`.
The inverse quadratic-form argument proves convexity of its entropy integrand.
Identifying its integral with relative entropy is a separate spectral calculation.
These are ingredients for Minsker's Fact 5, used in `app:ch_waves:thm:sampling`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker
open Matrix

namespace JanetCartan.OperatorBernstein.LiebConcavity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Matrix of `Z ↦ A*Z + t•(Z*X)` in column vectorization, for the
relative-entropy proof in `app:ch_waves:thm:sampling`. -/
def entropyResolventMatrix (X A : Matrix d d ℂ) (t : ℝ) : Matrix (d × d) (d × d) ℂ :=
  (1 : Matrix d d ℂ) ⊗ₖ A + t • (Xᵀ ⊗ₖ (1 : Matrix d d ℂ))

/-- Resolvent integrand whose integral represents unnormalized matrix relative
entropy (`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
def relativeEntropyResolvent (X A : Matrix d d ℂ) (t : ℝ) : ℝ :=
  inverseQuadraticForm (entropyResolventMatrix X A t) X.vec - realTrace X / (1 + t)

/-- Positivity of the relative-entropy resolvent operator for nonnegative parameters
(`app:ch_waves:thm:sampling`). -/
lemma posDef_entropyResolventMatrix {X A : Matrix d d ℂ}
    (hX : X.PosDef) (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (entropyResolventMatrix X A t).PosDef := by
  exact (Matrix.PosDef.one.kronecker hA).add_posSemidef
    ((hX.transpose.posSemidef.kronecker Matrix.PosSemidef.one).smul ht)

omit [Fintype d] in
/-- The resolvent matrix depends linearly on both entropy arguments
(`app:ch_waves:thm:sampling`). -/
lemma entropyResolventMatrix_mix (X Y A B : Matrix d d ℂ) (a b t : ℝ) :
    entropyResolventMatrix (a • X + b • Y) (a • A + b • B) t =
      a • entropyResolventMatrix X A t + b • entropyResolventMatrix Y B t := by
  simp only [entropyResolventMatrix, kronecker_add, kronecker_smul,
    transpose_add, transpose_smul, add_kronecker, smul_kronecker, smul_add]
  module

/-- Action of the Kronecker resolvent on a vectorized matrix
(`app:ch_waves:thm:sampling`). -/
lemma entropyResolventMatrix_mulVec (X A Z : Matrix d d ℂ) (t : ℝ) :
    entropyResolventMatrix X A t *ᵥ Z.vec = (A * Z + t • (Z * X)).vec := by
  simp [entropyResolventMatrix, add_mulVec, smul_mulVec, kronecker_mulVec_vec]

omit [Fintype d] [DecidableEq d] in
/-- The joint positive-definite entropy domain is convex, including empty indices
(`app:ch_waves:thm:sampling`). -/
lemma convex_posDef_pairs :
    Convex ℝ {p : Matrix d d ℂ × Matrix d d ℂ | p.1.PosDef ∧ p.2.PosDef} := by
  intro p hp q hq a b ha hb hab
  exact ⟨convex_posDef hp.1 hq.1 ha hb hab, convex_posDef hp.2 hq.2 ha hb hab⟩

/-- Joint convexity of each relative-entropy resolvent integrand. The proof uses
completion of a square, and imposes no commutativity condition
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem convexOn_relativeEntropyResolvent {t : ℝ} (ht : 0 ≤ t) :
    ConvexOn ℝ {p : Matrix d d ℂ × Matrix d d ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => relativeEntropyResolvent p.1 p.2 t) := by
  refine ⟨convex_posDef_pairs, ?_⟩
  intro p hp q hq a b ha hb hab
  have h := (convexOn_inverseQuadraticForm (d := d × d)).2
    (x := (entropyResolventMatrix p.1 p.2 t, p.1.vec))
    (y := (entropyResolventMatrix q.1 q.2 t, q.1.vec))
    (posDef_entropyResolventMatrix hp.1 hp.2 ht)
    (posDef_entropyResolventMatrix hq.1 hq.2 ht) ha hb hab
  change inverseQuadraticForm
    (a • entropyResolventMatrix p.1 p.2 t + b • entropyResolventMatrix q.1 q.2 t)
    (a • p.1.vec + b • q.1.vec) ≤
    a * inverseQuadraticForm (entropyResolventMatrix p.1 p.2 t) p.1.vec +
    b * inverseQuadraticForm (entropyResolventMatrix q.1 q.2 t) q.1.vec at h
  change relativeEntropyResolvent (a • p.1 + b • q.1) (a • p.2 + b • q.2) t ≤ _
  simp only [relativeEntropyResolvent, entropyResolventMatrix_mix, vec_add, vec_smul,
    realTrace, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re,
    smul_eq_mul, add_div, mul_div_assoc]
  linarith

end JanetCartan.OperatorBernstein.LiebConcavity
