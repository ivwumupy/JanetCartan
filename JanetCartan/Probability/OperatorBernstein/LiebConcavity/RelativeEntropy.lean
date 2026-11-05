module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Resolvent
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Spectral

/-!
# Joint convexity of matrix relative entropy

The inverse quadratic form makes the matrix resolvent integrand jointly convex.
Its spectral representation proves integrability and identifies its integral with
unnormalized relative entropy. Integrating the convexity inequality therefore proves
`convexOn_relativeEntropy` on pairs of positive-definite matrices.

This is a prerequisite for Minsker's Fact 5, used in
`app:ch_waves:thm:sampling` of `paper.tex`. All finite index types are allowed,
including the empty type, without a commutativity assumption.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder

namespace JanetCartan.OperatorBernstein.LiebConcavity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Integration preserves the joint convexity of the entropy resolvent, provided
its integrability is supplied. The spectral representation discharges this premise
in `convexOn_relativeEntropy`
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem convexOn_integral_relativeEntropyResolvent
    (hInt : ∀ (X A : Matrix d d ℂ), X.PosDef → A.PosDef →
      IntegrableOn (relativeEntropyResolvent X A) (Set.Ioi 0)) :
    ConvexOn ℝ {p : Matrix d d ℂ × Matrix d d ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => ∫ t : ℝ in Set.Ioi 0, relativeEntropyResolvent p.1 p.2 t) := by
  apply integral_convexOn_of_integrand_ae convex_posDef_pairs
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact convexOn_relativeEntropyResolvent ht.le
  · intro p hp
    exact hInt p.1 p.2 hp.1 hp.2

/-- Joint convexity of unnormalized finite-dimensional matrix relative entropy,
the entropy ingredient for Minsker's Fact 5 used in `app:ch_waves:thm:sampling`.
The resolvent integral proves the inequality for arbitrary positive-definite pairs,
including matrices indexed by the empty type. -/
theorem convexOn_relativeEntropy :
    ConvexOn ℝ {p : Matrix d d ℂ × Matrix d d ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => relativeEntropy p.1 p.2) := by
  have hconv := convexOn_integral_relativeEntropyResolvent (d := d)
    (fun _ _ hX hA => integrableOn_relativeEntropyResolvent hX hA)
  exact hconv.congr (fun _ hp => (relativeEntropy_eq_integral_resolvent hp.1 hp.2).symm)

end JanetCartan.OperatorBernstein.LiebConcavity
