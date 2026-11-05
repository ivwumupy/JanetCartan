module

public import JanetCartan.Iteration.RevisedUniform.OriginalCore
public import JanetCartan.Iteration.RevisedAssembly.Initialization
public meta import JanetCartan.Iteration.RevisedUniform.OriginalTargetTemplate

/-!
# Original-target reduction on the actual inverse defect core

The native correction acts on the fixed original χ₂ core D, not the larger
pre-existing G.domain.core. The original contracted reference and its domain
are unchanged. Restrict the target bounds to the ACTUAL D, then use the existing
revised recursion, convergence and same-coordinate restoration. The genuine
UniformHistoryCorrection on D remains explicit: this target/domain deduction
does not prove the analytic uniform step or unconditional Main.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RevisedUniform.OriginalTarget

/-- The actual fixed inverse core reaches the SAME reference chart through
its native PDE ball and native Sobolev domain. There is no patch selection and
the reference domain is not modified (`main:prop:seed`). -/
theorem native_core_subset_reference_chart {n : ℕ} (D U : Set (Euclidean n))
    (χ₂ : ContDiffBump (0 : Euclidean n)) (normRadius b R : ℝ) (G : FlatReference n)
    (hD : D ⊆ ball 0 χ₂.rIn) (hU : ball 0 χ₂.rIn ⊆ U)
    (hUW : U ⊆ ball 0 normRadius) (hNormBall : closedBall (0 : Euclidean n) normRadius ⊆ ball 0 b)
    (hbR : b < R) (hR : R < G.domain.chartRadius) :
    D ⊆ G.domain.chart n ∧ D ⊆ G.domain.closureChart n := by
  have hDb : D ⊆ ball (0 : Euclidean n) b :=
    ((hD.trans hU).trans hUW).trans (ball_subset_closedBall.trans hNormBall)
  have hchart : D ⊆ ball (0 : Euclidean n) G.domain.chartRadius :=
    hDb.trans (ball_subset_ball (hbR.trans hR).le)
  exact ⟨hchart, hchart.trans ball_subset_closedBall⟩


/-- Restrict the actual normalized target defect to the selected smaller
inverse core without replacing the reference domain (`main:eq:initial-error`). -/
theorem initial_defect_subcore_le_chart {n : ℕ} (G : FlatReference n)
    {r : ℝ} (hsub : closedBall (0 : Euclidean n) r ⊆ G.domain.closureChart n)
    {g : MetricField n} (hg : ContinuousOn g (G.domain.closureChart n)) :
    cNorm (closedBall (0 : Euclidean n) r) 0 (inducedMetric G.map - g) ≤
      cNorm (G.domain.closureChart n) 0 (g - inducedMetric G.map) := by
  have hflat : inducedMetric G.map = fun _ ↦ 1 := funext G.inducedMetric_eq_one
  have hc : ContinuousOn (g - inducedMetric G.map) (G.domain.closureChart n) := by
    rw [hflat]
    exact hg.sub continuousOn_const
  have hb := (isCompact_closedBall (0 : Euclidean n) G.domain.chartRadius).bddAbove_image hc.norm
  rw [← neg_sub g (inducedMetric G.map), cNorm_neg]
  apply cNorm_mono_set_of_bddAbove hsub
  intro j hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  simpa only [norm_iteratedFDeriv_zero, LocalDomain.closureChart] using hb

/-- The original target/coordinate reduction on the actual inverse subcore.
The reference domain is untouched. The same-reference uniform finite step
remains explicit; only the existing compact-core mismatch is discharged
(`main:prop:seed`, `main:thm:main`). -/
theorem exists_normalized_revised_step_reduction_on_subcore {n : ℕ} (G : FlatReference n)
    {r : ℝ} (hr : 0 < r)
    (hsub : closedBall (0 : Euclidean n) r ⊆ G.domain.closureChart n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {V : Set (Euclidean n)}
    (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V) (hg : IsRiemannianMetricOn g V) :
    ∃ A : MetricTensor n, IsUnit A ∧ coordinatePullback g A 0 = 1 ∧
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
        (∀ s ∈ Icc (0 : ℝ) s₀,
          (∀ x ∈ G.domain.closureChart n, coordinateMap A ((s * ρ) • x) ∈ V) ∧
          IsRiemannianMetricOn (scaledMetric (coordinatePullback g A) (s * ρ))
            (G.domain.closureChart n)) ∧
        (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) s₀,
          cNorm (G.domain.closureChart n) m
            (scaledMetric (coordinatePullback g A) (s * ρ) - inducedMetric G.map) ≤ C * s) ∧
        ∀ cap : ℝ, 0 < cap → cap ≤ s₀ →
          ∀ (kMin : ℕ) (B Tref : ℝ) (C T : ℕ → ℝ),
            RevisedScales.cubicLoss n + 2 * growthExponent + 4 <
              (3 - 2 * growthExponent) * (kMin : ℝ) →
            RevisedGlobal.UniformHistoryCorrection G.map (closedBall (0 : Euclidean n) r)
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
  have htarget (s : ℝ) (hs : 0 < s) (hscap : s ≤ cap) :
      ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ)) (closedBall (0 : Euclidean n) r) :=
    ((hdom s ⟨hs.le, hscap.trans hcaps₀⟩).2.1.continuousOn).mono hsub
  have hinitial : ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
      cNorm (closedBall (0 : Euclidean n) r) 0
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
    exact (initial_defect_subcore_le_chart G hsub ((hdom s hsI).2.1.continuousOn)).trans
      ((hCbound s hsI).trans hsmall)
  exact hstep.exists_local_metric_of_initial_defects A hA hρ G.contDiff
    Metric.isOpen_ball (Metric.mem_ball_self hr) Metric.ball_subset_closedBall
    hV h0 htarget hgap hinitial

end JanetCartan.RevisedUniform.OriginalTarget

retain_actual_original_target_reduction
