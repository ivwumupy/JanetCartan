module

public import JanetCartan.Iteration.RevisedAssembly.Outer
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.CommonTarget

/-!
# Original-target reduction for one prescribed revised initializer

The backward boundary of `main:thm:main` and paper-v2 §18 `main:prop:seed`.
The flat reference and its positive source scale are prescribed, not reselected.
For the original local smooth positive metric, the existing target construction
provides normalized coordinates, one target interval and all finite-order bounds.
After ANY later positive cap and any finite-step thresholds, one positive target
dilation meets the initial defect required by the actual revised outer iteration.

The continuation still requires the genuine revised analytic finite-step producer
on this same reference and target. It does not count as unconditional existence.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RevisedAssembly

/-- `main:prop:seed`, `main:eq:initial-error`, and the final Euclidean consumer:
construct the original target inputs for one prescribed `G,ρ`. The complete
conditional continuation closes initialization, recursion, Bernstein, convergence,
and coordinate restoration. The ONLY remaining analytic input of that
continuation is the displayed same-reference revised uniform finite step. Its
constants precede every stage and the one final target dilation. -/
theorem exists_normalized_revised_step_reduction {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {V : Set (Euclidean n)}
    (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V) (hg : IsRiemannianMetricOn g V) :
    ∃ A : MetricTensor n, IsUnit A ∧ coordinatePullback g A 0 = 1 ∧
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
        (∀ s ∈ Icc (0 : ℝ) s₀,
          (∀ x ∈ G.domain.closureChart n, coordinateMap A ((s * ρ) • x) ∈ V) ∧
          IsRiemannianMetricOn (scaledMetric (coordinatePullback g A) (s * ρ))
            (G.domain.closureChart n)) ∧
        (∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) s₀,
          cNorm (G.domain.closureChart n) r
            (scaledMetric (coordinatePullback g A) (s * ρ) - inducedMetric G.map) ≤ C * s) ∧
        ∀ cap : ℝ, 0 < cap → cap ≤ s₀ →
          ∀ (kMin : ℕ) (B Tref : ℝ) (C T : ℕ → ℝ),
            RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
              (3 - 2 * growthExponent) * (kMin : ℝ) →
            RevisedGlobal.UniformHistoryCorrection G.map (G.domain.core n)
              (fun s ↦ scaledMetric (coordinatePullback g A) (s * ρ))
              cap kMin B Tref C T →
            ∃ U : Set (Euclidean n), IsOpen U ∧ (0 : Euclidean n) ∈ U ∧ U ⊆ V ∧
              ∃ F : Euclidean n → Euclidean (embeddingDimension n),
                ContDiffOn ℝ ∞ F U ∧ IsIsometricOn g F U := by
  obtain ⟨A, hA, hVA, hVA0, hgA, hgA0⟩ := exists_normalized_coordinates hV h0 hg
  obtain ⟨s₀, hs₀, hs₁, hdom, hbound⟩ :=
    local_target_bounds_for_fixed_reference G hρ hVA hVA0 hgA hgA0
  refine ⟨A, hA, hgA0, s₀, hs₀, hs₁, hdom, hbound, ?_⟩
  intro cap hcap hcaps₀ kMin B Tref C T hgap hstep
  have hsub : G.domain.core n ⊆ G.domain.closureChart n :=
    Metric.closedBall_subset_closedBall G.domain.coreRadius_lt_chartRadius.le
  have htarget (s : ℝ) (hs : 0 < s) (hscap : s ≤ cap) :
      ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ)) (G.domain.core n) :=
    ((hdom s ⟨hs.le, hscap.trans hcaps₀⟩).2.1.continuousOn).mono hsub
  have hinitial : ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
      cNorm (G.domain.core n) 0
        (inducedMetric G.map - scaledMetric (coordinatePullback g A) (s * ρ)) ≤ η := by
    intro η hη
    obtain ⟨C₀, hC₀, hCbound⟩ := hbound 0
    let s := min cap (η / C₀)
    have hs : 0 < s := lt_min hcap (div_pos hη hC₀)
    have hscap : s ≤ cap := min_le_left _ _
    have hsI : s ∈ Icc (0 : ℝ) s₀ := ⟨hs.le, hscap.trans hcaps₀⟩
    have hsmall : C₀ * s ≤ η := by
      rw [mul_comm]
      exact (le_div_iff₀ hC₀).mp (min_le_right _ _)
    refine ⟨s, hs, hscap, ?_⟩
    exact (initial_defect_core_le_chart G ((hdom s hsI).2.1.continuousOn)).trans
      ((hCbound s hsI).trans hsmall)
  exact hstep.exists_local_metric_of_initial_defects A hA hρ G.contDiff
    Metric.isOpen_ball (Metric.mem_ball_self G.domain.coreRadius_pos)
    Metric.ball_subset_closedBall hV h0 htarget hgap hinitial

end JanetCartan.RevisedAssembly
