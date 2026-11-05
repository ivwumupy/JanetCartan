module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Jets
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.OneDimension
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise

/-!
# Smooth L² jet estimates for finite-order regularity

The finite-order Sobolev regularity argument in
`app:ch_regular:thm:exact-correction`, using the norms of `app:not:fourier`,
reduces to a scalar pointwise estimate. Combining the unit-cube scalar bound
with scalar-to-jet lifting gives the uniform smooth estimate in every dimension,
without compact-support or additional decay assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- The uniform smooth L² jet estimate with derivative budget `k + n + 1`
for the finite-order regularity argument in
`app:ch_regular:thm:exact-correction`, using the norms of `app:not:fourier`.
The constant is independent of the function and evaluation point. This holds
for every normed real target, in particular for finite-dimensional real Hilbert
spaces, and also in dimension zero. No compact-support or additional decay
assumption is needed. -/
theorem exists_smooth_jet_estimate (n k : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ v →
      (∀ l ≤ k + n + 1, MemLp (iteratedFDeriv ℝ l v) 2 volume) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j v x‖ ≤
        C * ∑ l ∈ Finset.range (k + n + 1 + 1),
          (eLpNorm (iteratedFDeriv ℝ l v) 2 volume).toReal := by
  obtain ⟨C, hC, hscalar⟩ := exists_smooth_scalar_pointwise_estimate n
  refine ⟨C, hC, ?_⟩
  intro v hv hmem j hj x
  simpa only [Nat.add_assoc] using
    smooth_jet_estimate_of_scalar (r := n + 1) volume hC hscalar hv
      (fun l hl ↦ hmem l (by omega)) hj x

end JanetCartan.LocalSobolev.FiniteOrder
