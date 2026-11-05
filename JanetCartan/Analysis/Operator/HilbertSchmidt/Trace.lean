module

public import JanetCartan.Analysis.Operator.HilbertSchmidt.Compact
public import Mathlib.Analysis.InnerProductSpace.Trace
/-!
# Positive normals and finite-dimensional traces

The trace estimates for `TT*` in `app:ch_waves:thm:sampling`. Compressions are
actual operators on finite-dimensional subspaces, and their traces are Mathlib's
`LinearMap.trace`.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The positive trace of `TT*` equals the squared Hilbert–Schmidt sum of `T` (`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_normal_eq (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) (hT : IsHilbertSchmidt b T) :
    positiveTrace c (T ∘L T.adjoint) = hilbertSchmidtSq b T := by
  rw [positiveTrace_normal, (isHilbertSchmidt_adjoint b c T hT).2]

/-- Positivity of the actual normal `TT*` (`app:ch_waves:thm:sampling`). -/
theorem normal_diagonal_nonneg (T : E →L[𝕜] F) (y : F) :
    0 ≤ RCLike.re (inner 𝕜 y ((T ∘L T.adjoint) y)) := by
  rw [ContinuousLinearMap.comp_apply, ← T.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  positivity

/-- Convergence of the normal diagonal sum (`app:ch_waves:thm:sampling`). -/
theorem IsHilbertSchmidt.summable_normal_diagonal {b : HilbertBasis ι 𝕜 E}
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt b T) (c : HilbertBasis κ 𝕜 F) :
    Summable (fun i ↦ RCLike.re (inner 𝕜 (c i) ((T ∘L T.adjoint) (c i)))) := by
  simpa only [IsHilbertSchmidt, ContinuousLinearMap.comp_apply, ← T.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using
    (isHilbertSchmidt_adjoint b c T hT).1

/-- Compression to a finite-dimensional subspace (`app:ch_waves:thm:sampling`). -/
def finiteCompression (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U]
    (A : F →L[𝕜] F) : U →L[𝕜] U :=
  U.orthogonalProjectionOnto ∘L A ∘L U.subtypeL

/-- A compressed normal is the normal of the projected operator (`app:ch_waves:thm:sampling`). -/
theorem finiteCompression_normal (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U]
    (T : E →L[𝕜] F) :
    finiteCompression U (T ∘L T.adjoint) =
      (U.orthogonalProjectionOnto ∘L T) ∘L (U.orthogonalProjectionOnto ∘L T).adjoint := by
  simp [finiteCompression, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

/-- In finite dimensions the diagonal sum is the real part of the ordinary trace (`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_eq_re_trace [Fintype κ] (c : OrthonormalBasis κ 𝕜 F)
    (A : F →L[𝕜] F) :
    positiveTrace c.toHilbertBasis A = RCLike.re (LinearMap.trace 𝕜 F A.toLinearMap) := by
  rw [LinearMap.trace_eq_sum_inner _ c]
  simp [positiveTrace, map_sum]

/-- Every finite-dimensional compression of `TT*` has trace bounded by the same
Hilbert–Schmidt sum (`app:ch_waves:thm:sampling`). -/
theorem trace_finiteCompression_normal_le (b : HilbertBasis ι 𝕜 E)
    (T : E →L[𝕜] F) (hT : IsHilbertSchmidt b T)
    (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U] :
    RCLike.re (LinearMap.trace 𝕜 U (finiteCompression U (T ∘L T.adjoint)).toLinearMap) ≤
      hilbertSchmidtSq b T := by
  let c := stdOrthonormalBasis 𝕜 U
  rw [← positiveTrace_eq_re_trace c, finiteCompression_normal,
    positiveTrace_normal_eq b c.toHilbertBasis _ (hT.comp_left U.orthogonalProjectionOnto).1]
  calc
    hilbertSchmidtSq b (U.orthogonalProjectionOnto ∘L T) ≤
        ‖U.orthogonalProjectionOnto‖ ^ 2 * hilbertSchmidtSq b T :=
      (hT.comp_left U.orthogonalProjectionOnto).2
    _ ≤ 1 ^ 2 * hilbertSchmidtSq b T := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) U.orthogonalProjectionOnto_norm_le 2)
        (tsum_nonneg (fun _ ↦ sq_nonneg _))
    _ = hilbertSchmidtSq b T := by ring

omit [CompleteSpace E] [CompleteSpace F] in
/-- Monotonicity of convergent positive diagonal sums (`app:ch_waves:thm:sampling`). -/
theorem positiveTrace_mono (c : HilbertBasis κ 𝕜 F) (A B : F →L[𝕜] F)
    (hA : ∀ y, 0 ≤ RCLike.re (inner 𝕜 y (A y)))
    (hAB : ∀ y, RCLike.re (inner 𝕜 y (A y)) ≤ RCLike.re (inner 𝕜 y (B y)))
    (hB : Summable (fun i ↦ RCLike.re (inner 𝕜 (c i) (B (c i))))) :
    positiveTrace c A ≤ positiveTrace c B := by
  exact (hB.of_nonneg_of_le (fun i ↦ hA (c i)) (fun i ↦ hAB (c i))).tsum_le_tsum
    (fun i ↦ hAB (c i)) hB
/-- Compression preserves the quadratic form on its finite-dimensional subspace
(`app:ch_waves:thm:sampling`). -/
theorem finiteCompression_inner (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U]
    (A : F →L[𝕜] F) (x y : U) :
    inner 𝕜 x (finiteCompression U A y) = inner 𝕜 (x : F) (A y) := by
  change inner 𝕜 x (U.orthogonalProjectionOnto (A y)) = _
  rw [← Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- Quadratic-form domination bounds finite-dimensional compression traces
(`app:ch_waves:thm:sampling`). -/
theorem trace_finiteCompression_mono (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U]
    (A B : F →L[𝕜] F)
    (hAB : ∀ y, RCLike.re (inner 𝕜 y (A y)) ≤ RCLike.re (inner 𝕜 y (B y))) :
    RCLike.re (LinearMap.trace 𝕜 U (finiteCompression U A).toLinearMap) ≤
      RCLike.re (LinearMap.trace 𝕜 U (finiteCompression U B).toLinearMap) := by
  let b := stdOrthonormalBasis 𝕜 U
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  simp only [map_sum, ContinuousLinearMap.coe_coe, finiteCompression_inner]
  exact Finset.sum_le_sum (fun i _ ↦ hAB (b i))

omit [CompleteSpace F] in
/-- Orthogonal compression does not increase the operator norm
(`app:ch_waves:thm:sampling`). -/
theorem norm_finiteCompression_le (U : Submodule 𝕜 F) [FiniteDimensional 𝕜 U]
    (A : F →L[𝕜] F) : ‖finiteCompression U A‖ ≤ ‖A‖ := by
  refine (finiteCompression U A).opNorm_le_bound (norm_nonneg A) ?_
  intro x
  exact (U.norm_orthogonalProjectionOnto_apply_le (A x)).trans (A.le_opNorm x)

end JanetCartan
