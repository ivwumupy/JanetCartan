module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Spectral.Coordinates
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Resolvent

/-!
# The entropy resolvent in independent eigenbases

Solving the Sylvester equation entrywise gives the inverse quadratic form as a
finite sum of scalar resolvents (`app:ch_waves:thm:sampling`, Minsker Fact 5).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder
open Matrix

namespace JanetCartan.OperatorBernstein.LiebConcavity.Spectral
set_option backward.isDefEq.respectTransparency false

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Scalar entry of the Frobenius resolvent pairing
(`app:ch_waves:thm:sampling`). -/
lemma scalar_resolvent_pairing (w : ℂ) (x a t : ℝ) :
    (star (w * (x : ℂ)) * (w * ((x / (a + t * x) : ℝ) : ℂ))).re =
      Complex.normSq w * x ^ 2 / (a + t * x) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- Spectral expansion of the inverse quadratic form for the entropy resolvent,
with independent eigenbases (`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma inverseQuadraticForm_entropy_eq_sum {X A : Matrix d d ℂ}
    (hX : X.PosDef) (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    inverseQuadraticForm (entropyResolventMatrix X A t) X.vec =
      ∑ i, ∑ j, Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j) *
        hX.1.eigenvalues j ^ 2 / (hA.1.eigenvalues i + t * hX.1.eigenvalues j) := by
  let U := hX.1.eigenvectorUnitary
  let V := hA.1.eigenvectorUnitary
  let W : Matrix d d ℂ := star V.val * U.val
  let C : Matrix d d ℂ := fun i j =>
    W i j * ((hX.1.eigenvalues j / (hA.1.eigenvalues i + t * hX.1.eigenvalues j) : ℝ) : ℂ)
  let Z : Matrix d d ℂ := V.val * C * star U.val
  have hc : diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * C +
      t • (C * diagonal (fun j => (hX.1.eigenvalues j : ℂ))) = star V.val * X * U.val := by
    rw [hermitian_coordinates hX.1 V]
    ext i j
    have hd : hA.1.eigenvalues i + t * hX.1.eigenvalues j ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (hA.eigenvalues_pos i)
        (mul_nonneg ht (hX.eigenvalues_pos j).le))
    have hd' : (hA.1.eigenvalues i : ℂ) + (t : ℂ) * (hX.1.eigenvalues j : ℂ) ≠ 0 := by
      exact_mod_cast hd
    simp only [Matrix.add_apply, diagonal_mul, Matrix.smul_apply, mul_diagonal, C, W,
      Complex.real_smul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul]
    dsimp only [U]
    field_simp [hd', mul_comm]
  have hz : entropyResolventMatrix X A t *ᵥ Z.vec = X.vec := by
    rw [entropyResolventMatrix_mulVec]
    change (A * (V.val * C * star U.val) + t • ((V.val * C * star U.val) * X)).vec = _
    rw [sylvester_coordinates hX.1 hA.1, hc]
    congr 1
    change V.val * (star V.val * X * U.val) * star U.val = X
    calc
      _ = (V.val * star V.val) * X * (U.val * star U.val) := by simp only [mul_assoc]
      _ = X := by simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul, mul_one]
  have hi : (entropyResolventMatrix X A t)⁻¹ *ᵥ X.vec = Z.vec := by
    rw [← hz, mulVec_mulVec, nonsing_inv_mul _
      ((isUnit_iff_isUnit_det _).mp (posDef_entropyResolventMatrix hX hA ht).isUnit), one_mulVec]
  rw [inverseQuadraticForm, hi, star_vec_dotProduct_vec]
  change realTrace (Xᴴ * (V.val * C * star U.val)) = _
  unfold realTrace
  rw [trace_pairing_coordinates, hermitian_coordinates hX.1 V]
  change realTrace (((star V.val * U.val) * diagonal (fun j => (hX.1.eigenvalues j : ℂ)))ᴴ * C) = _
  rw [realTrace_pairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_diagonal]
  exact scalar_resolvent_pairing (W i j) _ _ _

end JanetCartan.OperatorBernstein.LiebConcavity.Spectral
