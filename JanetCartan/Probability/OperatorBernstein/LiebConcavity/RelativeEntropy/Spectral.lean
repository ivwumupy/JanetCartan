module

public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.Variational
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Resolvent
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.ScalarIntegral
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity.RelativeEntropy.Spectral.Inverse

/-!
# The resolvent integral for matrix relative entropy

Independent eigenbases of the two positive-definite matrices express both the
resolvent and relative entropy as finite sums with squared overlap weights.
The scalar logarithmic integral then proves the matrix integral representation.
These are the spectral ingredients of Minsker Fact 5 used in
`app:ch_waves:thm:sampling` of `paper.tex`.

All finite index types are allowed, including the empty type. No commutativity
assumption is imposed, and the ambient matrix norm remains Frobenius.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder
open Matrix MeasureTheory

namespace JanetCartan.OperatorBernstein.LiebConcavity
set_option backward.isDefEq.respectTransparency false

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Spectral expansion of the entropy resolvent in independent eigenbases
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma relativeEntropyResolvent_eq_sum {X A : Matrix d d ℂ}
    (hX : X.PosDef) (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    relativeEntropyResolvent X A t = ∑ i, ∑ j,
      Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j) *
        (hX.1.eigenvalues j ^ 2 / (hA.1.eigenvalues i + t * hX.1.eigenvalues j) -
          hX.1.eigenvalues j / (1 + t)) := by
  have htrace : realTrace X / (1 + t) = ∑ i, ∑ j,
      Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j) *
        (hX.1.eigenvalues j / (1 + t)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, Klein.sum_normSq_unitary_column, one_mul]
    simp [realTrace, hX.1.trace_eq_sum_eigenvalues, Finset.sum_div]
  rw [relativeEntropyResolvent, Spectral.inverseQuadraticForm_entropy_eq_sum hX hA ht, htrace]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Absolute integrability of the matrix relative-entropy resolvent
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem integrableOn_relativeEntropyResolvent {X A : Matrix d d ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    IntegrableOn (relativeEntropyResolvent X A) (Set.Ioi 0) := by
  have hi (i j : d) :=
    (integrableOn_scalarEntropyResolvent (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)).const_mul
      (Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j))
  apply IntegrableOn.congr_fun
    (integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hi i j) _ measurableSet_Ioi
  intro t ht
  exact (relativeEntropyResolvent_eq_sum hX hA ht.le).symm

/-- The matrix resolvent integral equals unnormalized relative entropy
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
theorem relativeEntropy_eq_integral_resolvent {X A : Matrix d d ℂ}
    (hX : X.PosDef) (hA : A.PosDef) :
    relativeEntropy X A = ∫ t : ℝ in Set.Ioi 0, relativeEntropyResolvent X A t := by
  have hi (i j : d) :=
    (integrableOn_scalarEntropyResolvent (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)).const_mul
      (Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j))
  calc
    relativeEntropy X A = ∑ i, ∑ j,
        Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j) *
          hX.1.eigenvalues j *
            (Real.log (hX.1.eigenvalues j) - Real.log (hA.1.eigenvalues i)) :=
      Spectral.relativeEntropy_eq_sum hX.1 hA.1
    _ = ∫ t : ℝ in Set.Ioi 0, ∑ i, ∑ j,
        Complex.normSq ((star hA.1.eigenvectorUnitary * hX.1.eigenvectorUnitary) i j) *
          (hX.1.eigenvalues j ^ 2 / (hA.1.eigenvalues i + t * hX.1.eigenvalues j) -
            hX.1.eigenvalues j / (1 + t)) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi i j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_scalarEntropyResolvent
        (hX.eigenvalues_pos j) (hA.eigenvalues_pos i)]
      ring
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      (relativeEntropyResolvent_eq_sum hX hA ht.le).symm

end JanetCartan.OperatorBernstein.LiebConcavity
