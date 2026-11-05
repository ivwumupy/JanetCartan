module

public import JanetCartan.Iteration.PhysicalBackground.SourceBounds
public import JanetCartan.Iteration.PhysicalBackground.ResidualProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Continuity of the exact measured tangent-plus-mean residual

Keep the original index-one physical cutoff and factor two. Subtract the
literal centered representatives in the common output Hilbert space before
using the physical jet bound. A single uniform finite-jet neighborhood gives
both the small base-norm difference and a **fixed** high datum budget.
Consumer: the residual fields in the finite raw continuity argument for
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow PositiveBackground PhysicalBackground UniformStep.Periodization
open ProjectedStressFrame

variable {n N : ℕ}

/-- The true measured residual difference obeys the positive physical Sobolev
bound on the **original** index-one support. No norm of a difference of moving
operators is used (`app:ch_background:eq:bg-current-raising`). -/
theorem measuredSourceToL2_sub_gradeNorm_le {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q Q₀ : Euclidean n → Fin n → MetricTensor n) (R R₀ : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r))) (hQ₀ : ContDiffOn ℝ ∞ Q₀ (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (hR₀ : ContDiffOn ℝ ∞ R₀ (ball 0 (4 * r)))
    (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s
      (measuredSourceToL2 hr hcell Q R hQ hR - measuredSourceToL2 hr hcell Q₀ R₀ hQ₀ hR₀) ≤
      (2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card) *
        cNorm (closedBall 0 (3 * r)) s (cutReducedSource (FixedCutoffs.physical hr 1) Q R -
          cutReducedSource (FixedCutoffs.physical hr 1) Q₀ R₀) := by
  let θ := FixedCutoffs.physical (n := n) hr 1
  let f := cutReducedSource θ Q R
  let g := cutReducedSource θ Q₀ R₀
  have hθ : tsupport θ ⊆ ball 0 (3 * r) := by
    apply (FixedCutoffs.physical_tsupport hr 1).trans (ball_subset_ball _)
    norm_num
  have hθW := hθ.trans (ball_subset_ball (by linarith : 3 * r ≤ 4 * r))
  have hf : ContDiff ℝ ∞ f := contDiff_cutReducedSource isOpen_ball θ.contDiff hθW hQ hR
  have hg : ContDiff ℝ ∞ g := contDiff_cutReducedSource isOpen_ball θ.contDiff hθW hQ₀ hR₀
  have hs : tsupport (f - g) ⊆ closedBall 0 (3 * r) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hk
    have ht : x ∉ tsupport θ := fun hx ↦ hk (ball_subset_closedBall (hθ hx))
    have h1 := image_eq_zero_of_notMem_tsupport (fun hx ↦ ht (cutReducedSource_tsupport θ Q R hx))
    have h2 := image_eq_zero_of_notMem_tsupport (fun hx ↦ ht (cutReducedSource_tsupport θ Q₀ R₀ hx))
    exact hx (by simp only [f, g, Pi.sub_apply, h1, h2, sub_self])
  have pf := fixedCutReducedSource_periodic hr hcell hQ hR 1
  have pg := fixedCutReducedSource_periodic hr hcell hQ₀ hR₀ 1
  have pd : IsSmoothPeriodic (vectorPeriodization (f - g)) := ⟨pf.1.sub pg.1, pf.2.sub pg.2⟩
  have heq : sourceToL2 f pf - sourceToL2 g pg = sourceToL2 (f - g) pd := by
    apply Lp.ext
    exact (Lp.coeFn_sub ..).trans (((sourceToL2_coeFn f pf).sub (sourceToL2_coeFn g pg)).trans
      (sourceToL2_coeFn (f - g) pd).symm)
  have hm := sourceToL2_mem (f - g) pd s
  let S := periodicSobolevScale n (Euclidean n)
  have hfactor : S.gradeNorm s ((2 : ℝ) • sourceToL2 (f - g) pd) =
      2 * S.gradeNorm s (sourceToL2 (f - g) pd) := by
    rw [S.gradeNorm_eq ((S.level s).smul_mem (2 : ℝ) hm), S.gradeNorm_eq hm]
    change S.seminorm s ((2 : ℝ) • (⟨_, hm⟩ : S.level s)) = _
    simpa only [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      map_smul_eq_mul (S.seminorm s) (2 : ℝ) (⟨_, hm⟩ : S.level s)
  have hdiff : measuredSourceToL2 hr hcell Q R hQ hR - measuredSourceToL2 hr hcell Q₀ R₀ hQ₀ hR₀ =
      (2 : ℝ) • sourceToL2 (f - g) pd := by
    rw [← heq, smul_sub]
    simp only [measuredSourceToL2, fixedResidualToL2, f, g, θ, ← neg_smul, neg_neg]
  have hb := sourceToL2_gradeNorm_le (show 3 * r < 1 / 2 by linarith) (hf.sub hg) hs pd s
  rw [hdiff, hfactor]
  calc
    _ ≤ 2 * (Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card *
        cNorm (closedBall 0 (3 * r)) s (f - g)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card) *
        cNorm (closedBall 0 (3 * r)) s (f - g) := by ring

/-- The actual tangent-plus-mean source is smooth on its original chart;
this exact proof enters both measured `L²` classes in the current comparison
(`app:ch_background:eq:bg-current-raising`). -/
theorem tangentMean_smoothOn {W : Set (Euclidean n)} {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) {X₀ : Euclidean n → Euclidean n} (hX₀ : ContDiff ℝ ∞ X₀)
    {H : MetricField n} (hH : ContDiffOn ℝ ∞ H W) :
    ContDiffOn ℝ ∞ (linearizedMetric F (tangentVariation F X₀) + H) W :=
  (contDiff_linearizedMetric hF ((hF.fderiv_right (by simp)).clm_apply hX₀) (by simp)).contDiffOn.add hH

/-- A single prehistory primitive neighborhood furnishes both inverse-input
bounds at the same measured source. The actual high budget is the reference
grade plus one, independent even of the requested base accuracy. The mean
producer supplies the difference of its actual retained families on this
compact set; the projected frame and two immersion derivatives are literal. -/
theorem exists_measured_tangent_source_tolerance {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (X₀ : Euclidean n → Euclidean n) (hX₀ : ContDiff ℝ ∞ X₀)
    (F₀ : Euclidean n → Euclidean N) (hF₀ : ContDiff ℝ ∞ F₀)
    (hQ₀ : ContDiffOn ℝ ∞ (projectedStress F₀) (ball 0 (4 * r)))
    (H₀ : MetricField n) (hH₀ : ContDiffOn ℝ ∞ H₀ (ball 0 (4 * r))) (s : ℕ)
    {η : ℝ} (hη : 0 < η) :
    let K := closedBall (0 : Euclidean n) (3 * r)
    let S := periodicSobolevScale n (Euclidean n)
    let e₀ := measuredSourceToL2 hr hcell (projectedStress F₀)
      (linearizedMetric F₀ (tangentVariation F₀ X₀) + H₀) hQ₀ (tangentMean_smoothOn hF₀ hX₀ hH₀)
    ∃ δ > 0, ∀ (F : Euclidean n → Euclidean N) (hF : ContDiff ℝ ∞ F)
      (hQ : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (4 * r)))
      (H : MetricField n) (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r))),
      cNorm K (s + 2) (F - F₀) + cNorm K s (projectedStress F - projectedStress F₀) +
        cNorm K s (H - H₀) < δ →
      let e := measuredSourceToL2 hr hcell (projectedStress F)
        (linearizedMetric F (tangentVariation F X₀) + H) hQ (tangentMean_smoothOn hF hX₀ hH)
      e ∈ S.level s ∧ ‖e - e₀‖ ≤ η ∧ S.gradeNorm s e ≤ S.gradeNorm s e₀ + 1 := by
  intro K S e₀
  let C := 2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt (sobolevMultiindices n s).card
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let ε := min η 1 / (1 + C)
  have hden : 0 < 1 + C := by linarith
  have hε : 0 < ε := div_pos (lt_min hη zero_lt_one) hden
  obtain ⟨δ, hδ, hclose⟩ := exists_cutPhysicalResidual_sub_tolerance (isCompact_closedBall _ _)
    isOpen_ball (closedBall_subset_ball (by linarith : 3 * r < 4 * r))
    (FixedCutoffs.physical hr 1) (FixedCutoffs.physical hr 1).contDiff X₀ hX₀ F₀ hF₀
    (projectedStress F₀) hQ₀ H₀ hH₀ s hε
  refine ⟨δ, hδ, ?_⟩
  intro F hF hQ H hH hsmall e
  have hres := hclose F (projectedStress F) H hF hQ hH hsmall
  have he : e ∈ S.level s := measuredSourceToL2_mem ..
  have he₀ : e₀ ∈ S.level s := measuredSourceToL2_mem ..
  have hd := (S.level s).sub_mem he he₀
  have hb : S.gradeNorm s (e - e₀) ≤ min η 1 := calc
    _ ≤ C * _ := measuredSourceToL2_sub_gradeNorm_le hr hcell _ _ _ _ hQ hQ₀
      (tangentMean_smoothOn hF hX₀ hH) (tangentMean_smoothOn hF₀ hX₀ hH₀) s
    _ ≤ C * ε := mul_le_mul_of_nonneg_left hres.le hC
    _ ≤ (1 + C) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    _ = _ := mul_div_cancel₀ _ hden.ne'
  have hsum := ResponseTransfer.gradeNorm_add_le S hd he₀
  rw [sub_add_cancel] at hsum
  exact ⟨he, (S.norm_le_gradeNorm hd).trans (hb.trans (min_le_left _ _)),
    hsum.trans (by linarith only [hb.trans (min_le_right _ _)])⟩

end JanetCartan.PhysicalInverseContinuity
