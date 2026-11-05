module

public import JanetCartan.Analysis.Microlocal.NormalComparison.MatrixColumns.Basic
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Basic

/-!
# The Hilbert–Schmidt sum of the actual matrix input

For `app:ch_osc:eq:osc-normal-basic`, the full native matrix operator has
Hilbert–Schmidt square equal to the finite sum of the original column
squares.  The input Hilbert basis is arbitrary, and no output projection is
introduced.  Summability is proved before any infinite sum is identified.
-/

@[expose] public noncomputable section

open MeasureTheory ContinuousLinearMap

namespace JanetCartan.NormalComparison

variable {X J F : Type*} [MeasurableSpace X] [Fintype J]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Orthogonality of the native input coordinates gives the actual adjoint
square identity (`app:ch_osc:eq:osc-normal-basic`). -/
theorem norm_matrixColumnOperator_adjoint_sq (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) (g : F) :
    ‖(matrixColumnOperator μ T).adjoint g‖ ^ 2 = ∑ j, ‖(T j).adjoint g‖ ^ 2 := by
  rw [← (Pseudodifferential.finiteL2CoordinateIsometry μ).norm_map
    ((matrixColumnOperator μ T).adjoint g), PiLp.norm_sq_eq_of_L2]
  simp only [matrixColumnOperator_adjoint_coordinate]

/-- Assemble the genuine Hilbert–Schmidt properties of the same columns on
the entire native matrix input (`app:ch_osc:eq:osc-normal-basic`). -/
theorem matrixColumnOperator_hilbertSchmidt (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (c : HilbertBasis κ ℂ (Lp (EuclideanSpace ℂ J) 2 μ))
    (hT : ∀ j, IsHilbertSchmidt b (T j)) :
    IsHilbertSchmidt c (matrixColumnOperator μ T) ∧
      hilbertSchmidtSq c (matrixColumnOperator μ T) = ∑ j, hilbertSchmidtSq b (T j) := by
  obtain ⟨s, d, _⟩ := exists_hilbertBasis ℂ F
  have hj (j : J) := isHilbertSchmidt_adjoint b d (T j) (hT j)
  have hsum : HasSum (fun k : s ↦ ∑ j, ‖(T j).adjoint (d k)‖ ^ 2)
      (∑ j, hilbertSchmidtSq b (T j)) := by
    apply hasSum_sum
    intro j _
    exact (hj j).2 ▸ (hj j).1.hasSum
  have hs : HasSum (fun k : s ↦ ‖(matrixColumnOperator μ T).adjoint (d k)‖ ^ 2)
      (∑ j, hilbertSchmidtSq b (T j)) := by
    simpa only [norm_matrixColumnOperator_adjoint_sq] using hsum
  obtain ⟨hmat, heq⟩ := isHilbertSchmidt_adjoint d c
    (matrixColumnOperator μ T).adjoint hs.summable
  rw [adjoint_adjoint] at hmat heq
  exact ⟨hmat, heq.trans hs.tsum_eq⟩

/-- Actual column Hilbert–Schmidt bounds sum without any further analytic
input (`app:ch_osc:eq:osc-normal-basic`). -/
theorem matrixColumnOperator_hilbertSchmidt_bound (μ : Measure X)
    (T : J → Lp ℂ 2 μ →L[ℂ] F) {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (c : HilbertBasis κ ℂ (Lp (EuclideanSpace ℂ J) 2 μ))
    {B : J → ℝ} (hT : ∀ j, IsHilbertSchmidt b (T j) ∧ hilbertSchmidtSq b (T j) ≤ B j) :
    IsHilbertSchmidt c (matrixColumnOperator μ T) ∧
      hilbertSchmidtSq c (matrixColumnOperator μ T) ≤ ∑ j, B j := by
  obtain ⟨hhs, heq⟩ := matrixColumnOperator_hilbertSchmidt μ T b c (fun j ↦ (hT j).1)
  exact ⟨hhs, heq.trans_le (Finset.sum_le_sum fun j _ ↦ (hT j).2)⟩

end JanetCartan.NormalComparison
