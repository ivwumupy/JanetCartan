module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Klein
/-!
# Coordinates for the matrix entropy integral

Independent eigenbases turn the Sylvester operator into scalar multiplication.
These formulas support Minsker Fact 5 in `app:ch_waves:thm:sampling` of `paper.tex`.
-/

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder
open Matrix
@[expose] public noncomputable section

namespace JanetCartan.OperatorBernstein.LiebConcavity.Spectral
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Moving the Frobenius pairing into two unitary bases
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma trace_pairing_coordinates (B C : Matrix d d ℂ) (U V : Matrix.unitaryGroup d ℂ) :
    (Bᴴ * (V.val * C * star U.val)).trace =
      ((star V.val * B * U.val)ᴴ * C).trace := by
  simp only [← star_eq_conjTranspose, star_mul, star_star]
  rw [← mul_assoc, trace_mul_cycle]
  simp only [mul_assoc]

/-- Coordinates of a Hermitian matrix between its eigenbasis and a second
unitary basis (`app:ch_waves:thm:sampling`). -/
lemma hermitian_coordinates {X : Matrix d d ℂ} (hX : X.IsHermitian) (V : Matrix.unitaryGroup d ℂ) :
    star V.val * X * hX.eigenvectorUnitary.val =
    (star V.val * hX.eigenvectorUnitary.val) * diagonal (fun j => (hX.eigenvalues j : ℂ)) := by
  nth_rw 1 [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
    Function.comp_def, mul_assoc, Unitary.coe_star_mul_self, mul_one]

omit [DecidableEq d] in
/-- Entrywise expansion of the Frobenius pairing
(`app:ch_waves:thm:sampling`). -/
lemma realTrace_pairing_eq_sum (B C : Matrix d d ℂ) :
    realTrace (Bᴴ * C) = ∑ i, ∑ j, (star (B i j) * C i j).re := by
  simp only [realTrace, trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

/-- The Sylvester operator is entrywise diagonal in independent eigenbases
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma sylvester_coordinates {X A : Matrix d d ℂ} (hX : X.IsHermitian) (hA : A.IsHermitian)
    (C : Matrix d d ℂ) (t : ℝ) :
    A * (hA.eigenvectorUnitary.val * C * star hX.eigenvectorUnitary.val) +
      t • ((hA.eigenvectorUnitary.val * C * star hX.eigenvectorUnitary.val) * X) =
    hA.eigenvectorUnitary.val *
      (diagonal (fun i => (hA.eigenvalues i : ℂ)) * C +
        t • (C * diagonal (fun j => (hX.eigenvalues j : ℂ)))) *
      star hX.eigenvectorUnitary.val := by
  nth_rw 1 [hA.spectral_theorem]
  conv_lhs => enter [2, 2, 2]; rw [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  congr 1
  · simp only [mul_assoc, ← mul_assoc (star hA.eigenvectorUnitary.val)
      hA.eigenvectorUnitary.val, Unitary.coe_star_mul_self, one_mul]
  · congr 1
    simp only [mul_assoc, ← mul_assoc (star hX.eigenvectorUnitary.val)
      hX.eigenvectorUnitary.val, Unitary.coe_star_mul_self, one_mul]

/-- Relative entropy as a sum weighted by squared eigenbasis overlaps
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma relativeEntropy_eq_sum {X A : Matrix d d ℂ} (hX : X.IsHermitian) (hA : A.IsHermitian) :
    relativeEntropy X A = ∑ i, ∑ j,
      Complex.normSq ((star hA.eigenvectorUnitary * hX.eigenvectorUnitary) i j) *
        hX.eigenvalues j * (Real.log (hX.eigenvalues j) - Real.log (hA.eigenvalues i)) := by
  have hn (i j : d) :
      Complex.normSq ((star hX.eigenvectorUnitary * hA.eigenvectorUnitary) j i) =
      Complex.normSq ((star hA.eigenvectorUnitary * hX.eigenvectorUnitary) i j) := by
    have he : star (star hA.eigenvectorUnitary * hX.eigenvectorUnitary) =
        star hX.eigenvectorUnitary * hA.eigenvectorUnitary := by simp
    rw [← he]
    change Complex.normSq (star ((star hA.eigenvectorUnitary * hX.eigenvectorUnitary) i j)) = _
    exact Complex.normSq_conj _
  have hself : (∑ j, hX.eigenvalues j * Real.log (hX.eigenvalues j)) =
      ∑ i, ∑ j, Complex.normSq ((star hA.eigenvectorUnitary * hX.eigenvectorUnitary) i j) *
        hX.eigenvalues j * Real.log (hX.eigenvalues j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, Klein.sum_normSq_unitary_column, one_mul]
  unfold relativeEntropy
  rw [mul_sub]
  simp only [realTrace, trace_sub, Complex.sub_re]
  change realTrace (X * CFC.log X) - realTrace (X * CFC.log A) = _
  rw [Klein.realTrace_mul_log_self_eq_sum hX, CFC.log,
    Klein.realTrace_mul_cfc_eq_sum hX hA, hself, Finset.sum_comm (f := fun j i =>
      hX.eigenvalues j * Real.log (hA.eigenvalues i) *
        Complex.normSq ((star hX.eigenvectorUnitary * hA.eigenvectorUnitary) j i))]
  simp_rw [hn, ← Finset.sum_sub_distrib]
  congr 1
  ext i
  congr 1
  ext j
  ring

end JanetCartan.OperatorBernstein.LiebConcavity.Spectral
