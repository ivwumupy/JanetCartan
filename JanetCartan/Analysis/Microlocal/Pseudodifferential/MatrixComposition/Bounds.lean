module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.MatrixIntegrals

/-!
# Primitive Frobenius source bounds

For `app:ch_regular_base:thm:actual-calculus`, bounds on the separate matrix
jets imply the entrywise bounds used by the scalar composition proofs. The
conversion constant depends only on the fixed finite matrix spaces.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius ContDiff
namespace JanetCartan.Pseudodifferential
variable {I J : Type} [Fintype I] [Fintype J]

-- Use the topology carried by the chosen norm when forming operator norms.
local instance : TopologicalSpace (Matrix I J ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := I) (n := J) (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- `app:ch_regular_base:thm:actual-calculus`: real-linear entry evaluation
on the complex Frobenius matrix space, for source differentiation. -/
def matrixEntryCLM (i : I) (j : J) : Matrix I J ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj (R := ℂ) (i, j)).comp matrixEntryEquiv.toContinuousLinearMap).restrictScalars ℝ

/-- `app:ch_regular_base:thm:actual-calculus`: a dimension-dependent bound
for all entry evaluations with the Frobenius matrix norm. -/
def matrixEntryBound (I J : Type) [Fintype I] [Fintype J] : ℝ :=
  ∑ i : I, ∑ j : J, ‖matrixEntryCLM i j‖

/-- `app:ch_regular_base:thm:actual-calculus`: the fixed coordinate constant
is nonnegative, including for empty matrix dimensions. -/
theorem matrixEntryBound_nonneg : 0 ≤ matrixEntryBound I J := by
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))

/-- `app:ch_regular_base:thm:actual-calculus`: every entry evaluation has
operator norm at most the common finite coordinate constant. -/
theorem norm_matrixEntryCLM_le (i : I) (j : J) : ‖matrixEntryCLM i j‖ ≤ matrixEntryBound I J := by
  apply (Finset.single_le_sum (fun k _ ↦ norm_nonneg (matrixEntryCLM i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)) (Finset.mem_univ i)

/-- `app:ch_regular_base:thm:actual-calculus`: a primitive Frobenius source
jet bound gives an entrywise source jet bound without using extra derivatives. -/
theorem norm_iteratedFDeriv_matrix_entry_le
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V → Matrix I J ℂ) (n d : ℕ) (hd : d ≤ n)
    (ha : ContDiff ℝ n a) (y : V) (i : I) (j : J) :
    ‖iteratedFDeriv ℝ d (fun z ↦ a z i j) y‖ ≤
      matrixEntryBound I J * ‖iteratedFDeriv ℝ d a y‖ := by
  have h := (matrixEntryCLM i j).norm_iteratedFDeriv_comp_left (x := y) ha.contDiffAt
    (show (d : ℕ∞ω) ≤ n by exact_mod_cast hd)
  exact h.trans (mul_le_mul_of_nonneg_right (norm_matrixEntryCLM_le i j) (norm_nonneg _))
end JanetCartan.Pseudodifferential
