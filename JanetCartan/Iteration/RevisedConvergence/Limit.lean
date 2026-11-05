module

public import JanetCartan.Iteration.RevisedConvergence.Rates
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricLimit
public import JanetCartan.Geometry.IsometricEmbedding.Calculus

/-!
# One global revised smooth sum and the exact metric on the fixed core

The limiting argument in §18 (`main:eq:final-Cr` and
`main:eq:metric-induction`) of `paper-v2.tex`.  These deductions use the
literal revised derivative budgets along one adaptive staircase, and reuse
the smooth-series and metric-limit theorems.  There is one globally defined
real-valued sequence and one global sum; neither the map nor its domain is
chosen separately at each derivative order.

This file is conditional on the actual derivative and metric budgets.  Their
producers are the physical Bernstein theorem and the revised compatible
recursion, respectively.  It is not an unconditional existence theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RevisedConvergence

/-- The single global sum in §18 after `main:eq:final-Cr`. -/
def limitMap {n N : ℕ} (G : Euclidean n → Euclidean N)
    (u : ℕ → Euclidean n → Euclidean N) : Euclidean n → Euclidean N :=
  fun x ↦ G x + ∑' j, u j x

/-- `main:eq:final-Cr`: the revised budgets are summable for each actual
pointwise derivative of the same increment sequence. -/
theorem summable_iteratedFDeriv_of_revised_bounds {n N : ℕ}
    (H : ℕ → ℝ) (kMin : ℕ) {R₀ : ℝ} (hR₀ : 1 < R₀)
    {u : ℕ → Euclidean n → Euclidean N} {C : ℕ → ℝ}
    (hderiv : ∀ r, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ r (u j) x‖ ≤ derivativeBudget n H kMin R₀ C r j)
    (r : ℕ) (x : Euclidean n) :
    Summable (fun j ↦ iteratedFDeriv ℝ r (u j) x) := by
  apply Summable.of_norm_bounded_eventually (summable_derivativeBudget n H kMin hR₀ C r)
  rw [Nat.cofinite_eq_atTop]
  exact (hderiv r).mono (fun _ hj ↦ hj x)

/-- §18 after `main:eq:final-Cr`: the literal revised decay gives one globally
smooth sum, uniform convergence of every derivative on the entire source,
and the exact target metric on the original compact core.  Continuity of the
actual defect is proved before its `cNorm` is used as a pointwise bound. -/
theorem smooth_isometric_limit_of_revised_bounds {n N : ℕ}
    (H : ℕ → ℝ) (kMin : ℕ) {R₀ : ℝ} (hR₀ : 1 < R₀)
    {G : Euclidean n → Euclidean N} {u : ℕ → Euclidean n → Euclidean N}
    {D : Set (Euclidean n)} {g : MetricField n} {C : ℕ → ℝ}
    (hD : IsCompact D) (hG : ContDiff ℝ ∞ G)
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (hg : ContinuousOn g D)
    (hderiv : ∀ r, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ r (u j) x‖ ≤ derivativeBudget n H kMin R₀ C r j)
    (hmetric : ∀ j, cNorm D 0 (inducedMetric (currentHistoryMap G u j) - g) ≤
      (iterationScale R₀ growthExponent j ^
        (-(powerAdaptiveSchedule H R₀ growthExponent kMin j : ℝ))) ^ 2) :
    ContDiff ℝ ∞ (limitMap G u) ∧
      (∀ r : ℕ, TendstoUniformly
        (fun j ↦ iteratedFDeriv ℝ r (currentHistoryMap G u j))
        (iteratedFDeriv ℝ r (limitMap G u)) atTop) ∧
      IsIsometricOn g (limitMap G u) D := by
  have hsum := summable_derivativeBudget n H kMin hR₀ C
  obtain ⟨hsmooth, hconv⟩ := smooth_limit_of_eventual_bounds hG hu hsum hderiv
  refine ⟨hsmooth, hconv, ?_⟩
  apply isIsometricOn_series_of_metric_error hG hu hsum hderiv
    (tendsto_metricBudget H kMin hR₀)
  intro j x hx
  have hM : ContDiff ℝ ∞ (currentHistoryMap G u j) :=
    hG.add (ContDiff.sum (fun i _ ↦ hu i))
  have hcont := ((contDiff_inducedMetric hM (r := 0) (by simp)).continuous.continuousOn.sub
    hg).norm
  have hb := hD.bddAbove_image hcont
  have hpoint : ‖(inducedMetric (currentHistoryMap G u j) - g) x‖ ≤
      cNorm D 0 (inducedMetric (currentHistoryMap G u j) - g) := by
    rw [cNorm_order_zero]
    exact le_csSup hb (Set.mem_image_of_mem _ hx)
  exact hpoint.trans (hmetric j)

end JanetCartan.RevisedConvergence
