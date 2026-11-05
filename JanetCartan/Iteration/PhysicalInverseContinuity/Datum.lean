module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Stress
public import JanetCartan.Iteration.PhysicalDensityContinuity.Prescribed

/-!
# Measured datum transfer for the retained finite physical family

The input below is exactly the conclusion of the physical density continuity
producer, not a continuity bound on an inverse or a residual. Its original
source application supplies that input for the literal charts and amplitudes.
The reference datum is fixed before *all* grades and requested accuracies.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalInverseContinuity
open ProjectedStressFrame ContinuumRow PositiveBackground PhysicalBackground

/-- Compose the retained mean producer on its exact compact chart with the
actual index-one measurement and projected-frame stability. This produces the
source membership and low/high bounds at one fixed reference datum and the
same `current` chart, for `app:ch_background:prop:bg-normalized`. -/
theorem exists_measured_retained_source_tolerance {n : ℕ} {ι : Type} [Fintype ι]
    (G : FlatReference n) {μ R : ℝ} (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2)
    (hR : 6 * μ < G.domain.chartRadius)
    {C : (Euclidean n → Euclidean (embeddingDimension n)) → Type}
    {d₀ : ι → CarrierData n (embeddingDimension n)}
    {d : ∀ F, C F → ι → CarrierData n (embeddingDimension n)}
    {χ : ι → CarrierParameter → ℝ}
    (hmean : ∀ (s : ℕ) {ε : ℝ}, 0 < ε → ∃ δ > 0,
      ContDiffOn ℝ ∞ (physicalDensityMean d₀ χ 0) (ball 0 (4 * μ)) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)), ContDiff ℝ ∞ F →
        cNorm (closedBall 0 (max R (6 * μ))) (max 8 (s + 6)) (F - G.map) < δ →
        ∀ c : C F, ContDiffOn ℝ ∞ (physicalDensityMean (d F c) χ 0) (ball 0 (4 * μ)) ∧
          cNorm (closedBall 0 (3 * μ)) s (physicalDensityMean (d F c) χ 0 - physicalDensityMean d₀ χ 0) < ε) :
    let H₀ := physicalDensityMean d₀ χ 0
    ∃ hQ₀ : ContDiffOn ℝ ∞ (projectedStress G.map) (ball 0 (4 * μ)),
    ∃ hH₀ : ContDiffOn ℝ ∞ H₀ (ball 0 (4 * μ)),
    ∀ (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀),
      let S := periodicSobolevScale n (Euclidean n)
      let e₀ := measuredSourceToL2 hμ hcell (projectedStress G.map)
        (linearizedMetric G.map (tangentVariation G.map X₀) + H₀) hQ₀ (tangentMean_smoothOn G.contDiff hX₀ hH₀)
      (∀ s, e₀ ∈ S.level s) ∧
      ∀ (s : ℕ) {η : ℝ}, 0 < η → ∃ δ > 0,
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F),
        cNorm (closedBall 0 (max R (6 * μ))) (max 8 (s + 6)) (F - G.map) < δ →
      ∀ c : C F,
        let H := physicalDensityMean (d F c) χ 0
        ∃ hQ : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (4 * μ)),
        ∃ hH : ContDiffOn ℝ ∞ H (ball 0 (4 * μ)),
        let e := measuredSourceToL2 hμ hcell (projectedStress F)
          (linearizedMetric F (tangentVariation F X₀) + H) hQ (tangentMean_smoothOn hF hX₀ hH)
        e ∈ S.level s ∧ ‖e - e₀‖ ≤ η ∧ S.gradeNorm s e ≤ S.gradeNorm s e₀ + 1 := by
  intro H₀
  have hQ₀ := (exists_measured_projectedStress_tolerance G hμ hR 0 zero_lt_one).1
  have hH₀ := (hmean 0 zero_lt_one).choose_spec.2.1
  refine ⟨hQ₀, hH₀, ?_⟩
  intro X₀ hX₀ S e₀
  refine ⟨fun s ↦ measuredSourceToL2_mem .., ?_⟩
  intro s η hη
  obtain ⟨_, dR, hdR, hres⟩ := exists_measured_source_tolerance_of_mean_jet G hμ hcell hR X₀ hX₀ H₀ hH₀ s hη
  obtain ⟨dM, hdM, _, hmeanNow⟩ := hmean s hdR
  refine ⟨min dR dM, lt_min hdR hdM, ?_⟩
  intro F hF hsmall c H
  have hsub : cNorm (closedBall 0 (6 * μ)) (max 8 (s + 2)) (F - G.map) ≤
      cNorm (closedBall 0 (max R (6 * μ))) (max 8 (s + 2)) (F - G.map) :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall (le_max_right _ _)) (isCompact_closedBall _ _)
      (fun _ _ ↦ (hF.sub G.contDiff).contDiffAt.of_le (by simp))
  have hnear := hsub.trans_lt ((cNorm_mono_order (show max 8 (s + 2) ≤ max 8 (s + 6) by omega)).trans_lt
    (hsmall.trans_le (min_le_left _ _)))
  obtain ⟨hQ, hnow⟩ := hres F hF hnear
  obtain ⟨hH, hdiff⟩ := hmeanNow F hF (hsmall.trans_le (min_le_right _ _)) c
  exact ⟨hQ, hH, hnow H hH hdiff⟩

end JanetCartan.PhysicalInverseContinuity
