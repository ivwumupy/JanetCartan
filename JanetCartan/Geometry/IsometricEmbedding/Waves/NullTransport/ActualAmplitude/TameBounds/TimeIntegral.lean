module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Composition
public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral

/-!
# Bounds for the literal characteristic time integral

For `app:ch_waves:eq:joint-tame`, rescale the time integral to the unit interval.
For each integration parameter the time rescaling is a contraction in the
actual product norm, and preserves balls centered on the initial section.
The existing dominated differentiation theorem then bounds every joint jet.
Multiplication by the time coordinate gives a linear estimate for the literal
variable-endpoint integral. No integral derivative is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.NullTransport.AmplitudeTame

open FullPhaseCharts.InverseEstimates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Time rescaling, keeping every spatial and carrier label fixed
(`app:ch_waves:eq:joint-tame`). -/
def timeSegment (s : ℝ) : (ℝ × E) →L[ℝ] ℝ × E :=
  (s • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)

/-- The time rescaling is a contraction in the original product norm
(`app:ch_waves:eq:joint-tame`). -/
theorem norm_timeSegment_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖timeSegment (E := E) s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖s * q.1‖ ‖q.2‖ ≤ 1 * ‖q‖
  rw [one_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact max_le ((mul_le_of_le_one_left (norm_nonneg _) hs.2).trans (norm_fst_le q))
    (norm_snd_le q)

/-- Each segment stays in the same ball around the initial section
(`app:ch_waves:eq:joint-tame`). -/
theorem dist_timeSegment_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (p : E) (q : ℝ × E) : dist (timeSegment s q) (0, p) ≤ dist q (0, p) := by
  have hfix : timeSegment s ((0 : ℝ), p) = (0, p) := by
    ext <;> simp [timeSegment]
  calc
    _ = ‖timeSegment s (q - (0, p))‖ := by rw [map_sub, hfix, dist_eq_norm]
    _ ≤ ‖timeSegment (E := E) s‖ * ‖q - (0, p)‖ :=
      (timeSegment (E := E) s).le_opNorm (q - (0, p))
    _ ≤ ‖q - (0, p)‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_timeSegment_le hs)
    _ = _ := (dist_eq_norm _ _).symm

variable [FiniteDimensional ℝ E]

/-- `app:ch_waves:eq:joint-tame`: smoothness of the actual rescaled integral
on a ball. The physical and carrier labels are differentiated jointly. -/
theorem contDiffOn_timeAverage {p : E} {σ : ℝ} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hball : closedBall (0, p) σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2))
      (ball (0, p) σ) := by
  apply contDiffOn_fixedIntervalIntegral
    (F := fun z : ℝ × (ℝ × E) ↦ c (z.1 * z.2.1, z.2.2)) isOpen_ball
  intro z hz
  have hs : z.1 ∈ Icc (0 : ℝ) 1 := by simpa using hz.1
  have hm : timeSegment z.1 z.2 ∈ closedBall (0, p) σ :=
    (dist_timeSegment_le hs p z.2).trans (mem_ball.mp hz.2).le
  exact (hc.contDiffAt (hU.mem_nhds (hball hm))).comp z
    ((contDiffAt_fst.mul contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)

/-- `app:ch_waves:eq:joint-tame`: the time average has a linear bound in the
coefficient on a fixed larger ball. Every integral jet is proved by dominated
differentiation, with no loss of derivatives. -/
theorem cNorm_timeAverage_le {p : E} {ρ σ : ℝ} (hρσ : ρ < σ)
    {U : Set (ℝ × E)} (hU : IsOpen U) (hball : closedBall (0, p) σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (m : ℕ) :
    cNorm (closedBall (0, p) ρ) m
        (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)) ≤
      (m + 1 : ℝ) * cNorm (closedBall (0, p) σ) m c := by
  let H : ℝ × (ℝ × E) → ℝ := fun z ↦ c (z.1 * z.2.1, z.2.2)
  have hH : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ ball (0, p) σ, ContDiffAt ℝ ∞ H z := by
    intro z hz
    have hm : timeSegment z.1 z.2 ∈ closedBall (0, p) σ :=
      (dist_timeSegment_le hz.1 p z.2).trans (mem_ball.mp hz.2).le
    exact (hc.contDiffAt (hU.mem_nhds (hball hm))).comp z
      ((contDiffAt_fst.mul contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  have hjet (j : ℕ) (hj : j ≤ m) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (q : ℝ × E) (hq : q ∈ ball (0, p) σ) :
      ‖iteratedFDeriv ℝ j (fun x ↦ H (s, x)) q‖ ≤ cNorm (closedBall (0, p) σ) m c := by
    have hm : timeSegment s q ∈ closedBall (0, p) σ :=
      (dist_timeSegment_le hs p q).trans (mem_ball.mp hq).le
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
      (timeSegment s) hU hc (hball hm) j).trans
    apply (mul_le_mul
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun w hw ↦ (hc.contDiffAt (hU.mem_nhds (hball hw))).of_le (by simp)) hm hj)
      (pow_le_one₀ (norm_nonneg _) (norm_timeSegment_le hs))
      (pow_nonneg (norm_nonneg _) _) (cNorm_nonneg _ _ _)).trans_eq
    exact mul_one _
  have hb (j : ℕ) (hj : j ≤ m) (q : ℝ × E) (hq : q ∈ closedBall (0, p) ρ) :
      ‖iteratedFDeriv ℝ j (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, H (s, q)) q‖ ≤
        cNorm (closedBall (0, p) σ) m c :=
    NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le isOpen_ball hH
      (fun i hi ↦ hjet i (hi.trans hj)) (closedBall_subset_ball hρσ hq)
  simpa using cNorm_le_sum_of_bounds
    (fun _ _ ↦ cNorm_nonneg (closedBall (0, p) σ) m c) hb

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `app:ch_waves:thm:leading`: the literal time integral is time times the
unit-interval average. This identity includes negative times and time zero. -/
theorem timeIntegral_eq_time_mul_average (c : ℝ × E → ℝ) (q : ℝ × E) :
    (∫ s in (0 : ℝ)..q.1, c (s, q.2)) =
      q.1 * ∫ s in (0 : ℝ)..1, c (s * q.1, q.2) := by
  simpa only [mul_zero, zero_add, mul_one, add_zero, smul_eq_mul, mul_comm] using
    (intervalIntegral.smul_integral_comp_mul_add (fun s ↦ c (s, q.2))
      (a := 0) (b := 1) q.1 0).symm

/-- `app:ch_waves:eq:joint-tame`: the actual variable-endpoint time integral
is bounded linearly in the coefficient on a fixed buffered ball. The constant
depends only on the balls and the order, and precedes the coefficient. -/
theorem exists_cNorm_timeIntegral_le (p : E) {ρ σ : ℝ} (hρσ : ρ < σ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (ℝ × E)), IsOpen U → closedBall (0, p) σ ⊆ U →
      ∀ c : ℝ × E → ℝ, ContDiffOn ℝ ∞ c U →
        cNorm (closedBall (0, p) ρ) m (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) ≤
          C * cNorm (closedBall (0, p) σ) m c := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  let A : ℝ := ∑ j ∈ Finset.range (m + 1), ‖B‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  let T := cNorm (closedBall ((0 : ℝ), p) ρ) m (Prod.fst : ℝ × E → ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := cNorm_nonneg _ _ _
  refine ⟨1 + A * T * (m + 1), by positivity, ?_⟩
  intro U hU hball c hc
  have ha := contDiffOn_timeAverage hU hball hc
  have hb := cNorm_bilinear_le_on B (isCompact_closedBall (0, p) ρ) isOpen_ball
    (closedBall_subset_ball hρσ) contDiffOn_fst ha m
  have he : (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) =
      (fun q : ℝ × E ↦ B q.1 (∫ s in (0 : ℝ)..1, c (s * q.1, q.2))) :=
    funext (timeIntegral_eq_time_mul_average c)
  rw [he]
  apply hb.trans
  change A * T * cNorm (closedBall (0, p) ρ) m
      (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)) ≤ _
  apply (mul_le_mul_of_nonneg_left (cNorm_timeAverage_le hρσ hU hball hc m)
    (mul_nonneg hA hT)).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

/-- `app:ch_waves:eq:joint-tame`: the time average is smooth on an open
neighborhood of the whole working ball, including its boundary. This follows
from compactness of the coefficient domain, without assuming integral jets. -/
theorem exists_timeAverage_smooth_near_ball (p : E) {σ : ℝ} (hσ : 0 < σ)
    {U : Set (ℝ × E)} (hU : IsOpen U) (hball : closedBall (0, p) σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) :
    ∃ W : Set (ℝ × E), IsOpen W ∧ closedBall (0, p) σ ⊆ W ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)) W := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0, p) σ).exists_cthickening_subset_open hU hball
  rw [cthickening_closedBall hδ.le hσ.le] at hδU
  exact ⟨ball (0, p) (δ + σ), isOpen_ball, closedBall_subset_ball (by linarith),
    contDiffOn_timeAverage hU hδU hc⟩

/-- `app:ch_waves:eq:joint-tame`: the same compact ball at every order.
Continuity extends the proved interior estimate to the boundary, so no
order-dependent domain shrinkage is used. -/
theorem cNorm_timeAverage_le_same_ball (p : E) {σ : ℝ} (hσ : 0 < σ)
    {U : Set (ℝ × E)} (hU : IsOpen U) (hball : closedBall (0, p) σ ⊆ U)
    {c : ℝ × E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (m : ℕ) :
    cNorm (closedBall (0, p) σ) m
        (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)) ≤
      (m + 1 : ℝ) ^ 2 * cNorm (closedBall (0, p) σ) m c := by
  let f := fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)
  obtain ⟨W, hW, hKW, hf⟩ := exists_timeAverage_smooth_near_ball p hσ hU hball hc
  have hint (j : ℕ) (hj : j ≤ m) (q : ℝ × E) (hq : q ∈ ball (0, p) σ) :
      ‖iteratedFDeriv ℝ j f q‖ ≤ (m + 1 : ℝ) * cNorm (closedBall (0, p) σ) m c := by
    let ρ := (dist q (0, p) + σ) / 2
    have hρσ : ρ < σ := by dsimp [ρ]; linarith [mem_ball.mp hq]
    have hqρ : q ∈ closedBall (0, p) ρ := by
      rw [mem_closedBall]; dsimp [ρ]; linarith [mem_ball.mp hq]
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall (0, p) ρ)
      (fun y hy ↦ (hf.contDiffAt (hW.mem_nhds
        (hKW (closedBall_subset_closedBall hρσ.le hy)))).of_le (by simp)) hqρ hj).trans
    exact cNorm_timeAverage_le hρσ hU hball hc m
  have hb (j : ℕ) (hj : j ≤ m) (q : ℝ × E) (hq : q ∈ closedBall (0, p) σ) :
      ‖iteratedFDeriv ℝ j f q‖ ≤ (m + 1 : ℝ) * cNorm (closedBall (0, p) σ) m c := by
    have hq' : q ∈ closure (ball (0, p) σ) := by
      rwa [closure_ball _ hσ.ne']
    exact ContinuousWithinAt.closure_le hq'
      (((hf.contDiffAt (hW.mem_nhds (hKW hq))).continuousAt_iteratedFDeriv
        (show (j : ℕ∞ω) ≤ ∞ by simp)).norm.continuousWithinAt)
      continuousWithinAt_const (hint j hj)
  have hh := cNorm_le_sum_of_bounds
    (fun _ _ ↦ mul_nonneg (by positivity) (cNorm_nonneg (closedBall (0, p) σ) m c)) hb
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, pow_two, mul_assoc] using hh

/-- `app:ch_waves:eq:joint-tame`: linear bound for the literal time integral
on the identical compact ball used to measure its coefficient, at every order.
The constant is chosen before both the coefficient and its smoothness domain. -/
theorem exists_cNorm_timeIntegral_le_same_ball (p : E) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (ℝ × E)), IsOpen U → closedBall (0, p) σ ⊆ U →
      ∀ c : ℝ × E → ℝ, ContDiffOn ℝ ∞ c U →
        cNorm (closedBall (0, p) σ) m (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) ≤
          C * cNorm (closedBall (0, p) σ) m c := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  let A : ℝ := ∑ j ∈ Finset.range (m + 1), ‖B‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  let T := cNorm (closedBall ((0 : ℝ), p) σ) m (Prod.fst : ℝ × E → ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := cNorm_nonneg _ _ _
  refine ⟨1 + A * T * (m + 1) ^ 2, by positivity, ?_⟩
  intro U hU hball c hc
  obtain ⟨W, hW, hKW, ha⟩ := exists_timeAverage_smooth_near_ball p hσ hU hball hc
  have hb := cNorm_bilinear_le_on B (isCompact_closedBall (0, p) σ) hW hKW
    contDiffOn_fst ha m
  have he : (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) =
      (fun q : ℝ × E ↦ B q.1 (∫ s in (0 : ℝ)..1, c (s * q.1, q.2))) :=
    funext (timeIntegral_eq_time_mul_average c)
  rw [he]
  apply hb.trans
  change A * T * cNorm (closedBall (0, p) σ) m
      (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..1, c (s * q.1, q.2)) ≤ _
  apply (mul_le_mul_of_nonneg_left (cNorm_timeAverage_le_same_ball p hσ hU hball hc m)
    (mul_nonneg hA hT)).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)

end JanetCartan.NullTransport.AmplitudeTame
