module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational

/-!
# Klein's inequality for matrix relative entropy

The finite-dimensional inequality `Re tr X - Re tr Y ≤ D(X,Y)` supports the
variational proof of Minsker's Fact 5 (arXiv:1112.5448v3), used in
`app:ch_waves:thm:sampling` of `paper.tex`.

We diagonalize the two positive-definite matrices independently. Squared absolute
values of the entries of the unitary change of eigenbasis have row and column
sums one. Weighting the scalar logarithm inequality by these entries yields the
trace inequality. No commutativity, trace normalization, or nonempty index type
is required. The ambient matrix norm remains Frobenius.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder
open Matrix
namespace JanetCartan.OperatorBernstein.LiebConcavity
variable {d : Type*} [Fintype d] [DecidableEq d]

namespace Klein

/-- The scalar logarithm inequality used in Klein's inequality
(`app:ch_waves:thm:sampling`, variational proof of Minsker Fact 5). -/
theorem sub_le_mul_log_sub_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hdiv : x * (y / x - 1) = y - x := by field_simp
  rw [hdiv] at h
  nlinarith

/-- The squared absolute values in each row of a unitary matrix sum to one,
as used in the spectral proof of Klein's inequality (`app:ch_waves:thm:sampling`). -/
theorem sum_normSq_unitary_row (U : Matrix.unitaryGroup d ℂ) (i : d) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun M : Matrix d d ℂ => (M i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj] using h

/-- The squared absolute values in each column of a unitary matrix sum to one,
as used in the spectral proof of Klein's inequality (`app:ch_waves:thm:sampling`). -/
theorem sum_normSq_unitary_column (U : Matrix.unitaryGroup d ℂ) (j : d) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun M : Matrix d d ℂ => (M j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.normSq_apply] using h

/-- The trace pairing of two real diagonal matrices in different unitary bases,
expressed using squared overlaps (`app:ch_waves:thm:sampling`). -/
theorem realTrace_diagonal_mul_unitary_conj (a b : d → ℝ) (U : Matrix.unitaryGroup d ℂ) :
    realTrace (diagonal (fun i => (a i : ℂ)) *
      (U.val * diagonal (fun i => (b i : ℂ)) * star U.val)) =
    ∑ i, ∑ j, a i * b j * Complex.normSq (U i j) := by
  simp only [realTrace, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply (M := U.val * diagonal (fun i => (b i : ℂ))),
    Matrix.mul_diagonal, Matrix.star_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- Unitary conjugation preserves the real trace, as used in Klein's inequality
for `app:ch_waves:thm:sampling`. -/
theorem realTrace_unitary_conj (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    realTrace (Unitary.conjStarAlgAut ℂ _ U A) = realTrace A := by
  rw [realTrace, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rfl

/-- Moving a trace pairing into the first unitary basis leaves the relative
change of basis on the second factor (`app:ch_waves:thm:sampling`). -/
theorem realTrace_unitary_conj_mul_unitary_conj (U V : Matrix.unitaryGroup d ℂ) (A B : Matrix d d ℂ) :
    realTrace (Unitary.conjStarAlgAut ℂ _ U A * Unitary.conjStarAlgAut ℂ _ V B) =
      realTrace (A * Unitary.conjStarAlgAut ℂ _ (star U * V) B) := by
  rw [← realTrace_unitary_conj (star U)
    (Unitary.conjStarAlgAut ℂ _ U A * Unitary.conjStarAlgAut ℂ _ V B),
    map_mul, ← Unitary.conjStarAlgAut_mul_apply, ← Unitary.conjStarAlgAut_mul_apply]
  simp

/-- The spectral overlap formula for the trace pairing with a functional
calculus, used in Klein's inequality (`app:ch_waves:thm:sampling`). -/
theorem realTrace_mul_cfc_eq_sum {X Y : Matrix d d ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    realTrace (X * cfc f Y) = ∑ i, ∑ j,
      hX.eigenvalues i * f (hY.eigenvalues j) *
        Complex.normSq ((star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j) := by
  nth_rw 1 [hX.spectral_theorem]
  rw [hY.cfc_eq, Matrix.IsHermitian.cfc, realTrace_unitary_conj_mul_unitary_conj]
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
    realTrace_diagonal_mul_unitary_conj hX.eigenvalues (f ∘ hY.eigenvalues)
      (star hX.eigenvectorUnitary * hY.eigenvectorUnitary)

/-- The spectral formula for the unnormalized entropy term, used in the
variational proof of Minsker Fact 5 (`app:ch_waves:thm:sampling`). -/
theorem realTrace_mul_log_self_eq_sum {X : Matrix d d ℂ} (hX : X.IsHermitian) :
    realTrace (X * CFC.log X) = ∑ i, hX.eigenvalues i * Real.log (hX.eigenvalues i) := by
  rw [CFC.log, hX.cfc_eq, Matrix.IsHermitian.cfc]
  nth_rw 1 [hX.spectral_theorem]
  rw [← map_mul, realTrace_unitary_conj, Matrix.diagonal_mul_diagonal]
  simp [realTrace, Function.comp_def]

/-- Summing the scalar Klein inequality against unitary overlap weights gives
the spectral form of the matrix inequality (`app:ch_waves:thm:sampling`). -/
theorem sum_sub_le_log_sum_sub_weighted_log_sum (a b : d → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (U : Matrix.unitaryGroup d ℂ) :
    (∑ i, a i) - (∑ j, b j) ≤
      (∑ i, a i * Real.log (a i)) -
        ∑ i, ∑ j, a i * Real.log (b j) * Complex.normSq (U i j) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      mul_le_mul_of_nonneg_right (sub_le_mul_log_sub_log (ha i) (hb j))
        (Complex.normSq_nonneg (U i j))
  have hrow (v : d → ℝ) :
      (∑ i, ∑ j, v i * Complex.normSq (U i j)) = ∑ i, v i := by
    simp_rw [← Finset.mul_sum, sum_normSq_unitary_row, mul_one]
  have hcol (v : d → ℝ) :
      (∑ i, ∑ j, v j * Complex.normSq (U i j)) = ∑ j, v j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_normSq_unitary_column, mul_one]
  simp_rw [sub_mul, mul_sub, sub_mul, Finset.sum_sub_distrib] at h
  rw [hrow a, hcol b, hrow (fun i => a i * Real.log (a i))] at h
  exact h

end Klein

open Klein in
/-- Klein's inequality for unnormalized matrix relative entropy. This is the
entropy bound needed for the variational proof of Minsker's Fact 5, used in
`app:ch_waves:thm:sampling`. It holds for arbitrary finite index types, including
the empty type, without commutativity or trace normalization. -/
theorem realTrace_sub_le_relativeEntropy {X Y : Matrix d d ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    realTrace X - realTrace Y ≤ relativeEntropy X Y := by
  have hx : realTrace X = ∑ i, hX.1.eigenvalues i := by
    simp [realTrace, hX.1.trace_eq_sum_eigenvalues]
  have hy : realTrace Y = ∑ i, hY.1.eigenvalues i := by
    simp [realTrace, hY.1.trace_eq_sum_eigenvalues]
  rw [relativeEntropy, mul_sub]
  change realTrace X - realTrace Y ≤ realTrace (X * CFC.log X - X * CFC.log Y)
  have hsub (A B : Matrix d d ℂ) : realTrace (A - B) = realTrace A - realTrace B := by
    simp [realTrace]
  rw [hsub, realTrace_mul_log_self_eq_sum hX.1, CFC.log,
    realTrace_mul_cfc_eq_sum hX.1 hY.1, hx, hy]
  exact sum_sub_le_log_sum_sub_weighted_log_sum _ _ hX.eigenvalues_pos hY.eigenvalues_pos
    (star hX.1.eigenvectorUnitary * hY.1.eigenvectorUnitary)

end JanetCartan.OperatorBernstein.LiebConcavity
