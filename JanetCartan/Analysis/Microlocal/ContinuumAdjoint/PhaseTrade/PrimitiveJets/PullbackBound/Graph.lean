module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.PrimitiveJets.Extraction
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Carrier graph seminorms

The consumer is `exists_cNorm_transversePhaseGradientPullback_le_primitives`.
These projection estimates retain all carrier derivatives in
`app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint

/-- The carrier graph has a linear primitive seminorm bound on the working ball,
as used in `app:ch_regular_base:lem:buffered-interpolation`. -/
theorem cNorm_transverseCarrierGraph_le {n p : ℕ}
    (q₀ : Euclidean n × Euclidean p) (ρ : ℝ) (r : ℕ)
    {ζ : Euclidean p → Euclidean (n - 1)} (hζ : ContDiff ℝ ∞ ζ) :
    cNorm (Metric.closedBall q₀ ρ) r (fun q ↦ (q.1, ζ q.2)) ≤
      (r + 1 : ℕ) * (cNorm (Metric.closedBall q₀ ρ) r
        (Prod.fst : Euclidean n × Euclidean p → Euclidean n) +
          cNorm (Metric.closedBall q₀.2 ρ) r ζ) := by
  let P := ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean p)
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  have hb (j : ℕ) (hj : j ≤ r) (q : Euclidean n × Euclidean p)
      (hq : q ∈ Metric.closedBall q₀ ρ) :
      ‖iteratedFDeriv ℝ j (fun q ↦ (q.1, ζ q.2)) q‖ ≤
        cNorm (Metric.closedBall q₀ ρ) r
          (Prod.fst : Euclidean n × Euclidean p → Euclidean n) +
        cNorm (Metric.closedBall q₀.2 ρ) r ζ := by
    have hqz : q.2 ∈ Metric.closedBall q₀.2 ρ := by
      rw [Metric.mem_closedBall] at hq ⊢
      exact (le_max_right _ _).trans hq
    rw [iteratedFDeriv_prodMk (f := Prod.fst) (g := fun q ↦ ζ q.2)
      (x := q) contDiff_fst.contDiffAt
      (hζ.comp contDiff_snd).contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞),
      ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall q₀ ρ)
        contDiff_fst hq hj).trans (le_add_of_nonneg_right (cNorm_nonneg _ _ _))
    · have heq : (fun q : Euclidean n × Euclidean p ↦ ζ q.2) = ζ ∘ P := rfl
      rw [heq, P.iteratedFDeriv_comp_right hζ q (by simp : (j : ℕ∞ω) ≤ ∞)]
      apply ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_).trans
        (le_add_of_nonneg_left (cNorm_nonneg _ _ _))
      calc
        _ ≤ ‖iteratedFDeriv ℝ j ζ (P q)‖ * 1 :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
            (fun _ _ ↦ hP)) (norm_nonneg _)
        _ ≤ cNorm (Metric.closedBall q₀.2 ρ) r ζ := by
          rw [mul_one]
          exact norm_iteratedFDeriv_le_cNorm (isCompact_closedBall q₀.2 ρ)
            (hζ.of_le (by simp)) hqz hj
  simpa [mul_add] using cNorm_le_sum_of_bounds
    (fun _ _ ↦ add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)) hb

end JanetCartan.ContinuumAdjoint
