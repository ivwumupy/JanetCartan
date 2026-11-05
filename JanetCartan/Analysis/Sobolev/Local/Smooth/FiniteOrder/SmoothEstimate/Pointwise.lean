module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise.CubeEstimate

/-!
# From cube averaging to the smooth scalar Sobolev estimate

The iterated FTC estimate on a unit cube and its unit volume give a global
L² pointwise bound with constant `2 ^ n`, using derivatives through order `n`.
The scalar specialization supplies the derivative budget `n + 1` needed in
`app:ch_regular:thm:exact-correction`, with the norms of `app:not:fourier`.
No compact-support or additional decay assumption is required.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- Conversion of a local averaged-FTC estimate into the global Sobolev bound
of `app:not:fourier`. This discharges the integration and finiteness steps for
`app:ch_regular:thm:exact-correction`; the cube estimate is supplied separately.
The result uses only the derivative orders occurring in that premise. -/
theorem norm_le_sum_eLpNorm_of_pointwiseUnitCube_bound
    {n r : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : EuclideanSpace ℝ (Fin n) → F} (hu : ContDiff ℝ ∞ u)
    (hmem : ∀ l ≤ r, MemLp (iteratedFDeriv ℝ l u) 2 volume)
    {C : ℝ≥0} {x : EuclideanSpace ℝ (Fin n)}
    (hcube : ‖u x‖ₑ ≤ (C : ℝ≥0∞) * ∑ l ∈ Finset.range (r + 1),
      ∫⁻ y in pointwiseUnitCube x, ‖iteratedFDeriv ℝ l u y‖ₑ) :
    ‖u x‖ ≤ (C : ℝ) * ∑ l ∈ Finset.range (r + 1),
      (eLpNorm (iteratedFDeriv ℝ l u) 2 volume).toReal := by
  have hglobal : ‖u x‖ₑ ≤ (C : ℝ≥0∞) * ∑ l ∈ Finset.range (r + 1),
      eLpNorm (iteratedFDeriv ℝ l u) 2 volume := by
    apply hcube.trans
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro l _
    exact lintegral_enorm_pointwiseUnitCube_le_eLpNorm_two
      (f := iteratedFDeriv ℝ l u)
      (hu.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable x
  have hfinite (l : ℕ) (hl : l ∈ Finset.range (r + 1)) :
      eLpNorm (iteratedFDeriv ℝ l u) 2 volume ≠ ⊤ :=
    (hmem l (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)).ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simpa using hfinite)) hglobal
  simpa only [toReal_enorm, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum hfinite] using hreal

/-- A smooth function on `ℝⁿ` is bounded by `2 ^ n` times the sum of the global
L² norms of its derivatives through order `n`. This is the unit-cube Sobolev
estimate for `app:not:fourier`, used in `app:ch_regular:thm:exact-correction`.
It holds for arbitrary normed real targets, including in dimension zero. -/
theorem norm_le_sum_eLpNorm_iteratedFDeriv
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : EuclideanSpace ℝ (Fin n) → F} (hu : ContDiff ℝ ∞ u)
    (hmem : ∀ l ≤ n, MemLp (iteratedFDeriv ℝ l u) 2 volume)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖u x‖ ≤ (2 : ℝ) ^ n * ∑ l ∈ Finset.range (n + 1),
      (eLpNorm (iteratedFDeriv ℝ l u) 2 volume).toReal := by
  have h := norm_le_sum_eLpNorm_of_pointwiseUnitCube_bound
    (C := (2 : ℝ≥0) ^ n) hu hmem
    (by simpa using enorm_le_sum_lintegral_iteratedFDeriv_pointwiseUnitCube hu x)
  simpa using h

/-- The scalar smooth L² pointwise estimate for
`app:ch_regular:thm:exact-correction`, with the norms of `app:not:fourier` and
the derivative budget `n + 1`. The constant `2 ^ n` is independent of the
function and evaluation point; no support or additional decay assumption
is imposed. The estimate also holds in dimension zero. -/
theorem exists_smooth_scalar_pointwise_estimate (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ u →
      (∀ l ≤ n + 1, MemLp (iteratedFDeriv ℝ l u) 2 volume) →
      ∀ x, ‖u x‖ ≤ C * ∑ l ∈ Finset.range (n + 1 + 1),
        (eLpNorm (iteratedFDeriv ℝ l u) 2 volume).toReal := by
  refine ⟨(2 : ℝ) ^ n, by positivity, ?_⟩
  intro u hu hmem x
  refine (norm_le_sum_eLpNorm_iteratedFDeriv hu
    (fun l hl ↦ hmem l (Nat.le.step hl)) x).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  conv_rhs => rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

end JanetCartan.LocalSobolev.FiniteOrder
