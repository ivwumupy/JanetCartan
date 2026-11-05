module

public import JanetCartan.Probability.OperatorBernstein.TraceExponential
public import JanetCartan.Probability.OperatorBernstein.TailConversion.ScalarEstimates
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral event domination for operator Bernstein

The event inclusion needed in Minsker (3.2), for
`app:ch_waves:thm:sampling` of `paper.tex`. No equality between a spectral
remainder event and the largest-eigenvalue event is used.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Trace of the exponential remainder in Minsker (3.2), used in
`app:ch_waves:thm:sampling`. -/
def traceRemainder (θ : ℝ) (A : Matrix d d ℂ) : ℝ :=
  realTrace (NormedSpace.exp (θ • A) - θ • A - 1)

set_option backward.isDefEq.respectTransparency false in
/-- Functional calculus formula for the remainder in
`app:ch_waves:thm:sampling`, Minsker (3.2). -/
theorem cfc_expRemainder {A : Matrix d d ℂ} (hA : A.IsHermitian) (θ : ℝ) :
    cfc (fun x : ℝ ↦ expRemainder (θ * x)) A =
      NormedSpace.exp (θ • A) - θ • A - 1 := by
  have hf : (fun x : ℝ ↦ expRemainder (θ * x)) =
      (fun x : ℝ ↦ (Real.exp (θ * x) - 1) - θ • x) := by
    funext x
    simp only [expRemainder, smul_eq_mul]
    ring
  rw [hf, cfc_sub _ _ A, cfc_exp_mul_sub_one hA, cfc_smul_id θ A hA.isSelfAdjoint]
  abel

/-- The spectral sum formula for the trace remainder
(`app:ch_waves:thm:sampling`, Minsker (3.2)). -/
theorem traceRemainder_eq_sum {A : Matrix d d ℂ} (hA : A.IsHermitian) (θ : ℝ) :
    traceRemainder θ A = ∑ i, expRemainder (θ * hA.eigenvalues i) := by
  rw [traceRemainder, ← cfc_expRemainder hA, realTrace_cfc hA]

/-- Every summand of the spectral trace remainder is nonnegative
(`app:ch_waves:thm:sampling`). -/
theorem traceRemainder_nonneg {A : Matrix d d ℂ} (hA : A.IsHermitian) (θ : ℝ) :
    0 ≤ traceRemainder θ A := by
  rw [traceRemainder_eq_sum hA]
  exact Finset.sum_nonneg fun _ _ ↦ expRemainder_nonneg _

/-- A positive spectral value dominates its scalar remainder in the trace
(`app:ch_waves:thm:sampling`, Minsker (3.2)). -/
theorem expRemainder_le_traceRemainder_of_mem_spectrum {A : Matrix d d ℂ}
    (hA : A.IsHermitian) {θ t x : ℝ} (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (htx : t ≤ x) (hx : x ∈ spectrum ℝ A) :
    expRemainder (θ * t) ≤ traceRemainder θ A := by
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [traceRemainder_eq_sum hA]
  exact (expRemainder_mono (mul_nonneg hθ ht) (mul_le_mul_of_nonneg_left htx hθ)).trans
    (Finset.single_le_sum (f := fun i ↦ expRemainder (θ * hA.eigenvalues i))
      (fun _ _ ↦ expRemainder_nonneg _) (Finset.mem_univ i))

open scoped Matrix.Norms.L2Operator in
/-- The norm is a spectral value of one of the two signs of a Hermitian matrix
(`app:ch_waves:thm:sampling`). -/
theorem operatorNorm_mem_spectrum_or_neg {A : Matrix d d ℂ} [Nonempty d]
    (hA : A.IsHermitian) :
    operatorNorm A ∈ spectrum ℝ A ∨ operatorNorm A ∈ spectrum ℝ (-A) := by
  have h := CStarAlgebra.norm_or_neg_norm_mem_spectrum A hA.isSelfAdjoint
  change operatorNorm A ∈ spectrum ℝ A ∨ -operatorNorm A ∈ spectrum ℝ A at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← spectrum.neg_eq, Set.mem_neg]; exact h)

/-- Spectral event inclusion in Minsker (3.2), in a form that handles both signs
at once for `app:ch_waves:thm:sampling`. -/
theorem expRemainder_le_two_traceRemainders {A : Matrix d d ℂ}
    (hA : A.IsHermitian) {θ t : ℝ} (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (hAt : t < operatorNorm A) :
    expRemainder (θ * t) ≤ traceRemainder θ A + traceRemainder θ (-A) := by
  cases isEmpty_or_nonempty d with
  | inl hd =>
    have hzero : A = 0 := Subsingleton.elim _ _
    simp [hzero, operatorNorm] at hAt
    linarith
  | inr hd =>
    rcases operatorNorm_mem_spectrum_or_neg hA with h | h
    · exact (expRemainder_le_traceRemainder_of_mem_spectrum hA hθ ht hAt.le h).trans
        (le_add_of_nonneg_right (traceRemainder_nonneg hA.neg θ))
    · exact (expRemainder_le_traceRemainder_of_mem_spectrum hA.neg hθ ht hAt.le h).trans
        (le_add_of_nonneg_left (traceRemainder_nonneg hA θ))

end JanetCartan.OperatorBernstein
