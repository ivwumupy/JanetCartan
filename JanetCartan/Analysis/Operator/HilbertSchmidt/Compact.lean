module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
/-!
# Finite-rank approximation of Hilbert–Schmidt operators

The compactness step in `app:ch_waves:thm:sampling`, proved by convergence in
operator norm of the actual Hilbert-basis truncations.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open Filter
namespace JanetCartan

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Truncate the input expansion (`app:ch_waves:thm:sampling`). -/
def hilbertBasisTruncation (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (s : Finset ι) : E →L[𝕜] F :=
  ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (T (b i)) (b i)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Exact basis action of the finite-rank truncation
(`app:ch_waves:thm:sampling`). -/
theorem hilbertBasisTruncation_apply_basis [DecidableEq ι] (b : HilbertBasis ι 𝕜 E)
    (T : E →L[𝕜] F) (s : Finset ι) (i : ι) :
    hilbertBasisTruncation b T s (b i) = if i ∈ s then T (b i) else 0 := by
  classical
  simp [hilbertBasisTruncation, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Each basis truncation is compact (`app:ch_waves:thm:sampling`). -/
theorem isCompactOperator_hilbertBasisTruncation (b : HilbertBasis ι 𝕜 E)
    (T : E →L[𝕜] F) (s : Finset ι) : IsCompactOperator (hilbertBasisTruncation b T s) := by
  change hilbertBasisTruncation b T s ∈ compactOperator (RingHom.id 𝕜) E F
  apply Submodule.sum_mem
  intro i _
  change IsCompactOperator (InnerProductSpace.rankOne 𝕜 (T (b i)) (b i))
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (b i))).clm_comp
    (ContinuousLinearMap.toSpanSingleton 𝕜 (T (b i)))

omit [CompleteSpace E] [CompleteSpace F] in
/-- The squared Hilbert–Schmidt remainder is precisely the tail sum
(`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.truncation_remainder {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) (s : Finset ι) :
    IsHilbertSchmidt b (T - hilbertBasisTruncation b T s) ∧
    hilbertSchmidtSq b (T - hilbertBasisTruncation b T s) =
      hilbertSchmidtSq b T - ∑ i ∈ s, ‖T (b i)‖ ^ 2 := by
  classical
  let f : ι → ℝ := fun i ↦ if i ∈ s then ‖T (b i)‖ ^ 2 else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := s) (fun i hi ↦ by simp [f, hi])
  have heq (i : ι) : ‖(T - hilbertBasisTruncation b T s) (b i)‖ ^ 2 =
      ‖T (b i)‖ ^ 2 - f i := by
    rw [sub_apply, hilbertBasisTruncation_apply_basis]
    split_ifs <;> simp_all [f]
  constructor
  · simpa only [IsHilbertSchmidt, heq] using hT.sub hf
  · simp only [hilbertSchmidtSq, heq, hT.tsum_sub hf]
    rw [tsum_eq_sum (f := f) (s := s) (fun i hi ↦ by simp [f, hi])]
    simp [f]

/-- Finite-rank truncations converge in operator norm
(`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.tendsto_truncation {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) :
    Tendsto (hilbertBasisTruncation b T) atTop (nhds T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh : Tendsto (fun s : Finset ι ↦
      Real.sqrt (hilbertSchmidtSq b T - ∑ i ∈ s, ‖T (b i)‖ ^ 2)) atTop (nhds 0) := by
    simpa only [hilbertSchmidtSq, sub_self, Real.sqrt_zero, SummationFilter.unconditional_filter] using
      ((tendsto_const_nhds (x := hilbertSchmidtSq b T)).sub hT.hasSum).sqrt
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hh
  intro s
  rw [norm_sub_rev]
  have h := (hT.truncation_remainder s).1.opNorm_le
  rwa [(hT.truncation_remainder s).2] at h

/-- Hilbert–Schmidt operators are compact (`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.isCompactOperator {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) : IsCompactOperator T :=
  isCompactOperator_of_tendsto hT.tendsto_truncation
    (Eventually.of_forall (isCompactOperator_hilbertBasisTruncation b T))
end JanetCartan
