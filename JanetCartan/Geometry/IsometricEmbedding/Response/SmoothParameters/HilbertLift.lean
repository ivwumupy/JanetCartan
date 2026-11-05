module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Passing source derivatives through one bounded response

The finite-order step in the parameter paragraph of
`app:ch_response:thm:response-literal-transfer`. A bound on a fixed linear
response in a Hilbert source-jet norm extends that very map to the closure of
the source jets. Orthogonal projection is only an auxiliary extension device:
the result agrees on every original source, including its parameter derivatives.
The consumers are the compact output restrictions in `SmoothParameters`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseSmoothParameters

variable {V H G P : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A finite source-jet bound gives a continuous extension agreeing with the
SAME response on every original source (`app:ch_response:prop:response-graded`).
No density of the supported sources in the whole ambient Sobolev space is
assumed: extension first takes place in their own closed image. -/
theorem exists_response_extension_of_hilbert_bound
    (j : V →ₗ[ℝ] H) (B : V →ₗ[ℝ] G)
    (hB : ∃ C : ℝ, ∀ u, ‖B u‖ ≤ C * ‖j u‖) :
    ∃ A : H →L[ℝ] G, ∀ u, A (j u) = B u := by
  let S := j.range.topologicalClosure
  let e : V →ₗ[ℝ] S := j.codRestrict S fun u ↦
    j.range.le_topologicalClosure (LinearMap.mem_range_self j u)
  have hd : DenseRange e := by
    exact ((denseRange_inclusion_iff (s := Set.range j) subset_closure).2
      subset_rfl).comp Set.rangeFactorization_surjective.denseRange
      (continuous_inclusion subset_closure)
  let A : H →L[ℝ] G := (B.extendOfNorm e).comp S.orthogonalProjectionOnto
  refine ⟨A, fun u ↦ ?_⟩
  change B.extendOfNorm e (S.orthogonalProjectionOnto (e u : H)) = B u
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact LinearMap.extendOfNorm_eq hd hB u

/-- Smoothness in the actual finite source-jet norm implies smoothness after
the fixed response, without any output-parameter regularity premise
(`app:ch_response:thm:response-literal-transfer`). The bound is a producer input
on all original sources; it is not a bound on the selected family alone. -/
theorem contDiffAt_response_of_hilbert_bound
    (j : V →ₗ[ℝ] H) (B : V →ₗ[ℝ] G)
    (hB : ∃ C : ℝ, ∀ u, ‖B u‖ ≤ C * ‖j u‖)
    {f : P → V} {a : P} {k : ℕ∞ω}
    (hf : ContDiffAt ℝ k (fun c ↦ j (f c)) a) :
    ContDiffAt ℝ k (fun c ↦ B (f c)) a := by
  obtain ⟨A, hA⟩ := exists_response_extension_of_hilbert_bound j B hB
  simpa only [Function.comp_def, hA] using A.contDiff.contDiffAt.comp a hf

/-- Every evaluated parameter derivative commutes with the original response
whenever its source-jet derivative is the jet of the actual derivative source
(`app:ch_response:thm:response-literal-transfer`). This identity is pointwise
in the Banach output, not merely an identity between independent choices. -/
theorem iteratedFDeriv_response_eq_of_hilbert_bound
    (j : V →ₗ[ℝ] H) (B : V →ₗ[ℝ] G)
    (hB : ∃ C : ℝ, ∀ u, ‖B u‖ ≤ C * ‖j u‖)
    {f : P → V} {a : P} (k : ℕ) (v : Fin k → P) (df : V)
    (hf : ContDiffAt ℝ k (fun c ↦ j (f c)) a)
    (hd : iteratedFDeriv ℝ k (fun c ↦ j (f c)) a v = j df) :
    iteratedFDeriv ℝ k (fun c ↦ B (f c)) a v = B df := by
  obtain ⟨A, hA⟩ := exists_response_extension_of_hilbert_bound j B hB
  have he := congrArg (fun m ↦ m v) (A.iteratedFDeriv_comp_left hf le_rfl)
  simpa only [Function.comp_def, hA, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    hd] using he

end JanetCartan.ResponseSmoothParameters
