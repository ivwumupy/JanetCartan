module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Klein
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy

/-!
# Finite-dimensional Lieb trace concavity

Minsker's Fact 5 (arXiv:1112.5448v3) is used in the proof of (3.4), and hence in
`app:ch_waves:thm:sampling` of `paper.tex`.

Klein's inequality bounds the variational value by `Re tr exp(H + log A)`,
with equality at `X = exp(H + log A)`. Joint convexity of relative entropy
then bounds the convex combination of two maximizing values by the value at
the mixed matrices, proving concavity for every Hermitian `H`.

The ambient matrix norm remains Frobenius. No commutativity, trace normalization,
or nonempty index type is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder

namespace JanetCartan.OperatorBernstein.LiebConcavity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Klein's inequality bounds the variational expression by Lieb's trace
functional (`app:ch_waves:thm:sampling`, Minsker Fact 5). Together with
`variationalValue_exp_add_log`, this identifies its attained maximum. -/
theorem variationalValue_le_realTrace_exp_add_log {H X : Matrix d d ℂ}
    (hH : H.IsHermitian) (hX : X.PosDef) (A : Matrix d d ℂ) :
    variationalValue H X A ≤ realTrace (NormedSpace.exp (H + CFC.log A)) := by
  rw [variationalValue_eq_trace_sub_relativeEntropy hH]
  linarith [realTrace_sub_le_relativeEntropy hX (posDef_exp_add_log hH A)]

/-- Finite-dimensional Lieb trace concavity (Minsker, arXiv:1112.5448v3,
Fact 5), used in the proof of (3.4) and hence `app:ch_waves:thm:sampling`.
For every Hermitian `H`, the function `A ↦ Re tr exp(H + log A)` is concave
on the positive-definite cone. -/
theorem concaveOn_realTrace_exp_add_log {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix d d ℂ | A.PosDef}
      (fun A ↦ realTrace (NormedSpace.exp (H + CFC.log A))) := by
  refine ⟨convex_posDef, ?_⟩
  intro A hA B hB a b ha hb hab
  let X := NormedSpace.exp (H + CFC.log A)
  let Y := NormedSpace.exp (H + CFC.log B)
  have hX : X.PosDef := posDef_exp_add_log hH A
  have hY : Y.PosDef := posDef_exp_add_log hH B
  have hmix : (a • X + b • Y).PosDef := convex_posDef hX hY ha hb hab
  have hrel := convexOn_relativeEntropy.2
    (x := (X, A)) (y := (Y, B)) ⟨hX, hA⟩ ⟨hY, hB⟩ ha hb hab
  change relativeEntropy (a • X + b • Y) (a • A + b • B) ≤
    a * relativeEntropy X A + b * relativeEntropy Y B at hrel
  have hval := variationalValue_mix_sub_mix H X Y A B a b
  have hxval : variationalValue H X A = realTrace X := variationalValue_exp_add_log hH A
  have hyval : variationalValue H Y B = realTrace Y := variationalValue_exp_add_log hH B
  change a * realTrace X + b * realTrace Y ≤ _
  rw [hxval, hyval] at hval
  linarith [variationalValue_le_realTrace_exp_add_log hH hmix (a • A + b • B)]

/-- The `H = 0` case of Minsker's Fact 5, used in `app:ch_waves:thm:sampling`.
Here the trace functional equals the linear function `realTrace A`. -/
theorem concaveOn_realTrace_exp_zero_add_log :
    ConcaveOn ℝ {A : Matrix d d ℂ | A.PosDef}
      (fun A ↦ realTrace (NormedSpace.exp ((0 : Matrix d d ℂ) + CFC.log A))) := by
  refine ⟨convex_posDef, ?_⟩
  intro A hA B hB a b ha hb hab
  have hmix := convex_posDef hA hB ha hb hab
  simp only [zero_add, CFC.exp_log A hA.isStrictlyPositive,
    CFC.exp_log B hB.isStrictlyPositive, CFC.exp_log _ hmix.isStrictlyPositive]
  simp [realTrace]

end JanetCartan.OperatorBernstein.LiebConcavity
