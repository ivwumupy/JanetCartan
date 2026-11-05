module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Initial inputs to the outer iteration

The target estimate of `main:prop:seed` supplies the `htarget` and `hinitial`
arguments of `UniformHistoryCorrection.exists_local_embedding_of_initial_defects`
in `main:sec:convergence`. The reference and its positive source dilation are
fixed inputs. One positive parameter interval and an open neighborhood inside
the closed core are chosen before any accuracy or adaptive iteration threshold.

The defect in the iteration has the opposite sign to the initialization
estimate. Restriction to the core uses boundedness of the actual norm image on
the compact closed chart, obtained from local continuity. No global smoothness
of the metric is required.

These results do not construct a reference or a `UniformHistoryCorrection`.
The final assembly must supply those geometric and analytic inputs.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

private theorem initial_defect_cNorm_core_le {n : ℕ} (G : FlatReference n)
    {g : MetricField n} (hg : ContinuousOn g (G.domain.closureChart n)) :
    cNorm (G.domain.core n) 0 (inducedMetric G.map - g) ≤
      cNorm (G.domain.closureChart n) 0 (g - inducedMetric G.map) := by
  have hsub : G.domain.core n ⊆ G.domain.closureChart n :=
    Metric.closedBall_subset_closedBall G.domain.coreRadius_lt_chartRadius.le
  have hflat : inducedMetric G.map = fun _ ↦ 1 := funext G.inducedMetric_eq_one
  have hcont : ContinuousOn (g - inducedMetric G.map) (G.domain.closureChart n) := by
    rw [hflat]
    exact hg.sub continuousOn_const
  have hb : BddAbove
      ((fun x ↦ ‖(g - inducedMetric G.map) x‖) '' G.domain.closureChart n) :=
    (isCompact_closedBall (0 : Euclidean n) G.domain.chartRadius).bddAbove_image hcont.norm
  rw [← neg_sub g (inducedMetric G.map), cNorm_neg]
  apply cNorm_mono_set_of_bddAbove hsub
  intro j hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  simpa only [norm_iteratedFDeriv_zero] using hb

/-- `main:prop:seed` and `main:eq:initial-error`: for a fixed reference and a
locally smooth metric normalized at zero, choose the common positive interval
before all accuracies. The two last conjuncts are exactly the target continuity
and initial-defect hypotheses of
`UniformHistoryCorrection.exists_local_embedding_of_initial_defects`, with
`D = G.domain.core n`. The open neighborhood lies inside that core.

The reference must be supplied by its construction owner; this theorem makes
no assertion of a uniform history correction. -/
theorem exists_iteration_inputs_for_fixed_reference {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
        W ⊆ G.domain.core n ∧
        (∀ s, 0 < s → s ≤ s₀ →
          ContinuousOn (scaledMetric g (s * ρ)) (G.domain.core n)) ∧
        (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
          cNorm (G.domain.core n) 0
            (inducedMetric G.map - scaledMetric g (s * ρ)) ≤ η) := by
  obtain ⟨s₀, hs₀, hs₁, hdom, hb⟩ :=
    local_target_bounds_for_fixed_reference G hρ hU h0 hg hg0
  have hsub : G.domain.core n ⊆ G.domain.closureChart n :=
    Metric.closedBall_subset_closedBall G.domain.coreRadius_lt_chartRadius.le
  have hcont (s : ℝ) (hs : s ∈ Icc (0 : ℝ) s₀) :
      ContinuousOn (scaledMetric g (s * ρ)) (G.domain.closureChart n) :=
    (hdom s hs).2.1.continuousOn
  refine ⟨s₀, hs₀, hs₁, Metric.ball 0 G.domain.coreRadius, Metric.isOpen_ball,
    Metric.mem_ball_self G.domain.coreRadius_pos, Metric.ball_subset_closedBall,
    fun s hs hsmax ↦ (hcont s ⟨hs.le, hsmax⟩).mono hsub, ?_⟩
  intro η hη
  obtain ⟨C, hC, hbound⟩ := hb 0
  let s := min s₀ (η / C)
  have hs : 0 < s := lt_min hs₀ (div_pos hη hC)
  have hsmax : s ≤ s₀ := min_le_left _ _
  have hsI : s ∈ Icc (0 : ℝ) s₀ := ⟨hs.le, hsmax⟩
  have hsmall : C * s ≤ η := by
    rw [mul_comm]
    exact (le_div_iff₀ hC).mp (min_le_right _ _)
  exact ⟨s, hs, hsmax,
    (initial_defect_cNorm_core_le G (hcont s hsI)).trans
      ((hbound s hsI).trans hsmall)⟩

/-- `main:prop:seed` and `main:sec:convergence`: normalize an arbitrary local
smooth Riemannian metric and return the exact `htarget`, `hinitial`, and core
neighborhood inputs to
`UniformHistoryCorrection.exists_local_embedding_of_initial_defects`.
The coordinate change and interval precede every initial accuracy. The parent
construction must instantiate the fixed reference and source dilation, and
prove the uniform history correction on this same core and target interval. -/
theorem exists_normalized_iteration_inputs_for_reference {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (hg : IsRiemannianMetricOn g U) :
    ∃ A : MetricTensor n, IsUnit A ∧ coordinatePullback g A 0 = 1 ∧
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
        ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
          W ⊆ G.domain.core n ∧
          (∀ s, 0 < s → s ≤ s₀ →
            ContinuousOn (scaledMetric (coordinatePullback g A) (s * ρ))
              (G.domain.core n)) ∧
          (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧
            cNorm (G.domain.core n) 0
              (inducedMetric G.map - scaledMetric (coordinatePullback g A) (s * ρ)) ≤ η) := by
  obtain ⟨A, hA, hV, hV0, hgA, hgA0⟩ := exists_normalized_coordinates hU h0 hg
  exact ⟨A, hA, hgA0,
    exists_iteration_inputs_for_fixed_reference G hρ hV hV0 hgA hgA0⟩

end JanetCartan
