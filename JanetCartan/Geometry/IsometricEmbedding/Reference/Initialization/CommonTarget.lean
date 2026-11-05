module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# One target interval for initialization and smoothing

The common-interval assembly of `main:prop:seed` and `main:lem:smoothing`.
The actual linear initial-defect estimate survives every later positive cap.
The reference, source scale and normalizing coordinates are never changed.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan
open DefectSmoothing

/-- Restrict the reversed initial defect to the compact core, using actual
continuity to justify boundedness (`main:eq:seed-small`). -/
theorem initial_defect_core_le_chart {n : ℕ} (G : FlatReference n)
    {g : MetricField n} (hg : ContinuousOn g (G.domain.closureChart n)) :
    cNorm (G.domain.core n) 0 (inducedMetric G.map - g) ≤
      cNorm (G.domain.closureChart n) 0 (g - inducedMetric G.map) := by
  have hflat : inducedMetric G.map = fun _ ↦ 1 := funext G.inducedMetric_eq_one
  have hc : ContinuousOn (g - inducedMetric G.map) (G.domain.closureChart n) := by
    rw [hflat]
    exact hg.sub continuousOn_const
  have hb := (isCompact_closedBall (0 : Euclidean n) G.domain.chartRadius).bddAbove_image
    hc.norm
  rw [← neg_sub g (inducedMetric G.map), cNorm_neg]
  apply cNorm_mono_set_of_bddAbove
    (closedBall_subset_closedBall G.domain.coreRadius_lt_chartRadius.le)
  intro j hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  simpa only [norm_iteratedFDeriv_zero] using hb

/-- `main:prop:seed`: the target bounds and smoothing estimates hold on one
positive interval for the SAME reference and normalized metric. For any later
positive cap, a single dilation meets the initial-defect bound and all requested
finite-order accuracies. In particular the empty list supplies exactly
`hinitial` in `UniformHistoryCorrection.exists_local_embedding_of_initial_defects`.
The interval and constants precede every accuracy, initial scale and history. -/
theorem exists_common_target_initialization {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
        W ⊆ G.domain.core n ∧
        ∃ B L A C : ℕ → ℝ, (∀ r, 0 < B r) ∧
          (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ A r) ∧ (∀ k, 0 ≤ C k) ∧
          (∀ s ∈ Icc (0 : ℝ) s₀,
            (∀ x ∈ G.domain.closureChart n, (s * ρ) • x ∈ U) ∧
            IsRiemannianMetricOn (scaledMetric g (s * ρ)) (G.domain.closureChart n) ∧
            ContinuousOn (scaledMetric g (s * ρ)) (G.domain.core n) ∧
            (∀ r, cNorm (G.domain.closureChart n) r
              (scaledMetric g (s * ρ) - inducedMetric G.map) ≤ B r * s) ∧
            cNorm (G.domain.core n) 0
              (inducedMetric G.map - scaledMetric g (s * ρ)) ≤ B 0 * s) ∧
          (∀ cap : ℝ, 0 < cap → cap ≤ s₀ → ∀ η : ℝ, 0 < η →
            ∀ (orders : Finset ℕ) (ε : ℕ → ℝ), (∀ r ∈ orders, 0 < ε r) →
              ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
                cNorm (G.domain.core n) 0
                  (inducedMetric G.map - scaledMetric g (s * ρ)) ≤ η ∧
                ∀ r ∈ orders, cNorm (G.domain.closureChart n) r
                  (scaledMetric g (s * ρ) - inducedMetric G.map) < ε r) ∧
          (∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
            ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
              (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
            let R := iterationScale R₀ growthExponent j
            let δ := R ^ (-(k : ℝ))
            let gs := scaledMetric g (s * ρ)
            let e := historyDefect gs G.map u
            cNorm (G.domain.core n) 0 e ≤ δ ^ 2 →
            let eR := smoothedHistoryDefect G.domain R gs G.map u
            IsSmoothPeriodic eR ∧ HasFourierSupport (2 * R) eR ∧
            ((∀ x ∈ G.domain.core n, (gs x).IsSymm) → ∀ z, (eR z).IsSymm) ∧
            (∀ r (K : Set (Euclidean n)),
              cNorm K r (periodicLift eR) + periodicSobolevNorm (r : ℝ) eR ≤
                L r * δ ^ 2 * R ^ r) ∧
            (∀ r (K : Set (Euclidean n)),
              cNorm K r (periodicLift
                  (normalizedHistorySource G.domain R δ gs G.map u)) +
                periodicSobolevNorm (r : ℝ)
                  (normalizedHistorySource G.domain R δ gs G.map u) ≤
                A r * R ^ ((r : ℝ) - 2 * forcingExponent n)) ∧
            cNorm (G.domain.core n) 0 (e - periodicLift eR) ≤
              C k * δ * R ^ (-2 * (k : ℝ)) ∧
            (∀ x ∈ G.domain.core n, ‖periodicLift eR x - e x‖ ≤
              C k * δ * R ^ (-2 * (k : ℝ)))) := by
  obtain ⟨st, hst, hst1, hdom, hb⟩ :=
    local_target_bounds_for_fixed_reference G hρ hU h0 hg hg0
  obtain ⟨ss, hss, _, L, A, C, hL, hA, hC, hsmooth⟩ :=
    DefectSmoothing.exists_local_target_history_smoothing G.domain G hρ hU h0 hg.1 hg0 horder
  choose B hB hbound using hb
  let s₀ := min st ss
  have hs₀ : 0 < s₀ := lt_min hst hss
  have ht {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s₀) : s ∈ Icc (0 : ℝ) st :=
    ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s₀) := (hdom s (ht hs)).2.1.continuousOn
  have hinit {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s₀) :
      cNorm (G.domain.core n) 0
        (inducedMetric G.map - scaledMetric g (s * ρ)) ≤ B 0 * s :=
    (initial_defect_core_le_chart G (hc hs)).trans (hbound 0 s (ht hs))
  refine ⟨s₀, hs₀, (min_le_left _ _).trans hst1,
    ball 0 G.domain.coreRadius, isOpen_ball, mem_ball_self G.domain.coreRadius_pos,
    ball_subset_closedBall, B, L, A, C, hB, hL, hA, hC, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨(hdom s (ht hs)).1, (hdom s (ht hs)).2,
      (hc hs).mono (closedBall_subset_closedBall G.domain.coreRadius_lt_chartRadius.le),
      fun r ↦ hbound r s (ht hs), hinit hs⟩
  · intro cap hcap hcap0 η hη orders ε hε
    obtain ⟨s, hs, hsmax, hsε⟩ := exists_scale_for_finite_thresholds orders B ε hB hε
      (lt_min hcap (div_pos hη (hB 0)))
    have hscap := hsmax.trans (min_le_left cap (η / B 0))
    have hsI : s ∈ Icc (0 : ℝ) s₀ := ⟨hs.le, hscap.trans hcap0⟩
    have hsmall : B 0 * s ≤ η := by
      rw [mul_comm]
      exact (le_div_iff₀ (hB 0)).mp (hsmax.trans (min_le_right _ _))
    exact ⟨s, hs, hscap, (hinit hsI).trans hsmall,
      fun r hr ↦ (hbound r s (ht hsI)).trans_lt (hsε r hr)⟩
  · intro k s hs
    exact hsmooth k s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩

/-- Normalize an arbitrary local metric and fix one common interval for its
initialization and actual history smoothing (`main:prop:seed`,
`main:eq:normalized`, `main:eq:seed-small`). The same matrix, reference and source
scale are retained under every later positive cap and finite accuracy request. -/
theorem exists_normalized_common_target_initialization {n : ℕ} (G : FlatReference n)
    {ρ : ℝ} (hρ : 0 < ρ) {g : MetricField n} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U)
    (hg : IsRiemannianMetricOn g U) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ M : MetricTensor n, IsUnit M ∧ coordinatePullback g M 0 = 1 ∧
        ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
          ∃ W : Set (Euclidean n), IsOpen W ∧ (0 : Euclidean n) ∈ W ∧
            W ⊆ G.domain.core n ∧
            ∃ B L A C : ℕ → ℝ, (∀ r, 0 < B r) ∧
              (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ A r) ∧ (∀ k, 0 ≤ C k) ∧
              (∀ s ∈ Icc (0 : ℝ) s₀,
                (∀ x ∈ G.domain.closureChart n, coordinateMap M ((s * ρ) • x) ∈ U) ∧
                IsRiemannianMetricOn (scaledMetric (coordinatePullback g M) (s * ρ)) (G.domain.closureChart n) ∧
                ContinuousOn (scaledMetric (coordinatePullback g M) (s * ρ)) (G.domain.core n) ∧
                (∀ r, cNorm (G.domain.closureChart n) r
                  (scaledMetric (coordinatePullback g M) (s * ρ) - inducedMetric G.map) ≤ B r * s) ∧
                cNorm (G.domain.core n) 0
                  (inducedMetric G.map - scaledMetric (coordinatePullback g M) (s * ρ)) ≤ B 0 * s) ∧
              (∀ cap : ℝ, 0 < cap → cap ≤ s₀ → ∀ η : ℝ, 0 < η →
                ∀ (orders : Finset ℕ) (ε : ℕ → ℝ), (∀ r ∈ orders, 0 < ε r) →
                  ∃ s : ℝ, 0 < s ∧ s ≤ cap ∧
                    cNorm (G.domain.core n) 0
                      (inducedMetric G.map - scaledMetric (coordinatePullback g M) (s * ρ)) ≤ η ∧
                    ∀ r ∈ orders, cNorm (G.domain.closureChart n) r
                      (scaledMetric (coordinatePullback g M) (s * ρ) - inducedMetric G.map) < ε r) ∧
              (∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
                ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
                  (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
                let R := iterationScale R₀ growthExponent j
                let δ := R ^ (-(k : ℝ))
                let gs := scaledMetric (coordinatePullback g M) (s * ρ)
                let e := historyDefect gs G.map u
                cNorm (G.domain.core n) 0 e ≤ δ ^ 2 →
                let eR := smoothedHistoryDefect G.domain R gs G.map u
                IsSmoothPeriodic eR ∧ HasFourierSupport (2 * R) eR ∧
                ((∀ x ∈ G.domain.core n, (gs x).IsSymm) → ∀ z, (eR z).IsSymm) ∧
                (∀ r (K : Set (Euclidean n)),
                  cNorm K r (periodicLift eR) + periodicSobolevNorm (r : ℝ) eR ≤
                    L r * δ ^ 2 * R ^ r) ∧
                (∀ r (K : Set (Euclidean n)),
                  cNorm K r (periodicLift
                      (normalizedHistorySource G.domain R δ gs G.map u)) +
                    periodicSobolevNorm (r : ℝ)
                      (normalizedHistorySource G.domain R δ gs G.map u) ≤
                    A r * R ^ ((r : ℝ) - 2 * forcingExponent n)) ∧
                cNorm (G.domain.core n) 0 (e - periodicLift eR) ≤
                  C k * δ * R ^ (-2 * (k : ℝ)) ∧
                (∀ x ∈ G.domain.core n, ‖periodicLift eR x - e x‖ ≤
                  C k * δ * R ^ (-2 * (k : ℝ)))) := by
  obtain ⟨M, hM, hV, hV0, hgM, hgM0⟩ := exists_normalized_coordinates hU h0 hg
  exact ⟨M, hM, hgM0,
    exists_common_target_initialization G hρ hV hV0 hgM hgM0 horder⟩

end JanetCartan
