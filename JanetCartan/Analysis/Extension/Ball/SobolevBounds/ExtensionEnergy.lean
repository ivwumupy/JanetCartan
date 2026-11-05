module

public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.SeriesEstimate
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Fréchet energy bounds for the fixed extension

Assembly of the squared collar estimates and the interior restriction identity,
as in `app:ch_regular_base:eq:ball-extension-sobolev`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.BallExtension.Parameters

variable {n : ℕ} (p : Parameters (EuclideanSpace ℝ (Fin n)))

/-- The actual extension has the termwise exterior jets in the series argument
following `app:ch_regular_base:eq:extension-collar-l2`. -/
theorem iteratedFDeriv_extend_eq_tsum_exterior
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : p.radius < ‖x - p.center‖) :
    iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x =
      ∑' k, iteratedFDerivWithin ℝ m (fun y ↦ p.summand Seeley.coeff f y k)
        {y | p.radius ≤ ‖y - p.center‖} x := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv p.uniqueDiffOn_closedExterior
    ((p.contDiffAt_extend_exterior Seeley.coeff hf hx).of_le (by simp)) hx.le,
    iteratedFDerivWithin_congr
      (p.extend_eq_tsum_on_closedExterior Seeley.coeff (by simpa using Seeley.infinite_moment 0) f)
      hx.le m]
  exact p.iteratedFDerivWithin_tsum_summand_closedExterior Seeley.coeff
    Seeley.summable_abs_coeff_moment hf m hx.le

/-- The exterior derivative energy of the one fixed extension is bounded by
input jets through the same order (`app:ch_regular_base:eq:extension-collar-l2`). -/
theorem exists_integral_sq_norm_extend_radialCollar_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      (∫ x in p.radialCollar 0, ‖iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x‖ ^ 2) ≤
        C * frechetSobolevEnergy (ball p.center p.radius) m f := by
  obtain ⟨B, hB, hbound⟩ := p.exists_integral_sq_norm_summand_bound m
  let w : ℕ → ℝ := fun k ↦ |Seeley.coeff k| * (2 : ℝ) ^ (k * m)
  have hw : Summable w := Seeley.summable_abs_coeff_moment m
  have hw0 : ∀ k, 0 ≤ w k := fun k ↦ by dsimp [w]; positivity
  let S : ℝ := ∑' k, w k
  have hS : 0 ≤ S := tsum_nonneg hw0
  refine ⟨2 * B * S ^ 2, by positivity, ?_⟩
  intro f hf
  let J := frechetSobolevEnergy (ball p.center p.radius) m f
  have hJ : 0 ≤ J := frechetSobolevEnergy_nonneg _ _ _
  let v := fun k x ↦ iteratedFDerivWithin ℝ m (fun y ↦ p.summand Seeley.coeff f y k)
    {y | p.radius ≤ ‖y - p.center‖} x
  obtain ⟨u, hu, hmajor⟩ := p.exists_summable_summand_derivative_majorant Seeley.coeff
    Seeley.summable_abs_coeff_moment hf
  let μ := volume.restrict (p.radialCollar 0)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    ((measure_mono (p.radialCollar_subset_closedRadialCollar 0)).trans_lt
      (p.isCompact_closedRadialCollar 0).measure_lt_top).ne
  have hv : ∀ k, AEStronglyMeasurable (v k) μ := by
    intro k
    apply ContinuousOn.aestronglyMeasurable _ (p.isOpen_radialCollar 0).measurableSet
    exact ((p.contDiffOn_summand_closedExterior Seeley.coeff hf k).continuousOn_iteratedFDerivWithin
      (by simp) p.uniqueDiffOn_closedExterior).mono (fun _ hx ↦ hx.1.le)
  have hveq (k : ℕ) : (∫ x, ‖v k x‖ ^ 2 ∂μ) =
      ∫ x in p.radialCollar 0,
        ‖iteratedFDeriv ℝ m (fun y ↦ p.summand Seeley.coeff f y k) x‖ ^ 2 := by
    apply setIntegral_congr_fun (p.isOpen_radialCollar 0).measurableSet
    intro x hx
    dsimp only [v]
    rw [p.iteratedFDerivWithin_summand_eq_exterior Seeley.coeff hf k m hx.1]
  have hb : Summable (fun k ↦ B * S * w k * J) := (hw.mul_left (B * S)).mul_right J
  have h := integral_sq_norm_tsum_le_weighted_bound hv (hu m).abs
    (fun _ ↦ abs_nonneg _) (fun k ↦ by
      apply (ae_restrict_iff' (p.isOpen_radialCollar 0).measurableSet).mpr
      exact ae_of_all _ (fun x hx ↦ (hmajor m k x hx.1.le).trans (le_abs_self _)))
    hb (fun k ↦ by positivity) (fun k ↦ ?_)
  · calc
      _ = ∫ x, ‖∑' k, v k x‖ ^ 2 ∂μ := by
        apply setIntegral_congr_fun (p.isOpen_radialCollar 0).measurableSet
        intro x hx
        dsimp only
        rw [p.iteratedFDeriv_extend_eq_tsum_exterior hf m hx.1]
      _ ≤ 2 * ∑' k, B * S * w k * J := h
      _ = _ := by rw [tsum_mul_right, tsum_mul_left]; dsimp [S, J]; ring
  · rw [hveq]
    calc
      _ ≤ (2 : ℝ) ^ k *
          (B * |Seeley.coeff k| ^ 2 * (2 : ℝ) ^ (2 * k * m) / (2 : ℝ) ^ k * J) :=
        mul_le_mul_of_nonneg_left (hbound f hf Seeley.coeff k) (by positivity)
      _ = B * (w k) ^ 2 * J := by
        dsimp only [w]
        rw [mul_pow, ← pow_mul, show k * m * 2 = 2 * k * m by ring]
        field_simp
      _ ≤ B * S * w k * J := by
        have hk : w k ≤ S := hw.le_tsum k (fun i _ ↦ hw0 i)
        nlinarith [mul_nonneg hB (mul_nonneg (sub_nonneg.mpr hk) (hw0 k)), hJ]

/-- Exterior derivatives vanish outside the fixed collar in
`app:ch_regular_base:eq:extension-radial-formula`. -/
theorem iteratedFDeriv_extend_eq_zero_of_width_le
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : p.width ≤ ‖x - p.center‖ - p.radius) :
    iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x = 0 := by
  have he : p.radius < ‖x - p.center‖ := by linarith [p.width_pos]
  rw [p.iteratedFDeriv_extend_eq_tsum_exterior hf m he]
  suffices hz : ∀ k, iteratedFDerivWithin ℝ m
      (fun y ↦ p.summand Seeley.coeff f y k)
      {y | p.radius ≤ ‖y - p.center‖} x = 0 by simp only [hz, tsum_zero]
  intro k
  rw [p.iteratedFDerivWithin_summand_eq_exterior Seeley.coeff hf k m he]
  apply p.iteratedFDeriv_summand_eq_zero_of_width_le
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith [p.width_pos]

/-- Splitting the squared derivative integral into its original ball and collar,
with the sphere removed as a null set. Positive radius makes this valid also in
dimension zero (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem integral_sq_norm_extend_eq_ball_add_collar
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    (∫ x, ‖iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x‖ ^ 2) =
      (∫ x in ball p.center p.radius,
        ‖iteratedFDerivWithin ℝ m f (ball p.center p.radius) x‖ ^ 2) +
      ∫ x in p.radialCollar 0, ‖iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x‖ ^ 2 := by
  rw [← integral_add_compl measurableSet_closedBall
    (p.integrable_sq_norm_iteratedFDeriv_extend hf m)]
  congr 1
  · have heq : closedBall p.center p.radius =ᵐ[volume] ball p.center p.radius := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (Measure.addHaar_sphere_of_ne_zero volume p.center p.radius_pos.ne')] with x hx
      apply propext
      simp only [mem_closedBall_iff_norm, mem_ball_iff_norm]
      have hne : ‖x - p.center‖ ≠ p.radius := by simpa only [mem_sphere_iff_norm] using hx
      exact ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩
    rw [setIntegral_congr_set heq]
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [p.iteratedFDeriv_extend_eq_on_ball Seeley.coeff f m hx]
  · apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_closedBall.compl
      (fun x hx ↦ ?_)
    · intro x hx
      have he : p.radius < ‖x - p.center‖ := by
        simpa only [mem_compl_iff, mem_closedBall_iff_norm, not_le] using hx.1
      have hw : p.width ≤ ‖x - p.center‖ - p.radius := by
        by_contra! h
        exact hx.2 ⟨he, by simpa using h⟩
      simp [p.iteratedFDeriv_extend_eq_zero_of_width_le hf m hw]
    · exact fun h ↦ (not_le.mpr hx.1) (mem_closedBall_iff_norm.mp h)

/-- Every whole-space derivative integral of the fixed extension is bounded by
the input energy through that order (`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem exists_integral_sq_norm_extend_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      (∫ x, ‖iteratedFDeriv ℝ m (p.extend Seeley.coeff f) x‖ ^ 2) ≤
        C * frechetSobolevEnergy (ball p.center p.radius) m f := by
  obtain ⟨C, hC, hb⟩ := p.exists_integral_sq_norm_extend_radialCollar_bound m
  refine ⟨1 + C, by positivity, ?_⟩
  intro f hf
  rw [p.integral_sq_norm_extend_eq_ball_add_collar hf m, add_mul, one_mul]
  apply add_le_add _ (hb f hf)
  unfold frechetSobolevEnergy
  apply Finset.single_le_sum (a := m)
  · intro j _
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  · exact Finset.mem_range.mpr (Nat.lt_succ_self m)

/-- All-order auxiliary Fréchet energy estimate for the same Seeley formula.
No order-dependent choice of extension is made
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem exists_frechetSobolevEnergy_extend_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      frechetSobolevEnergy univ m (p.extend Seeley.coeff f) ≤
        C * frechetSobolevEnergy (ball p.center p.radius) m f := by
  choose C hC hb using p.exists_integral_sq_norm_extend_bound
  refine ⟨1 + ∑ j ∈ Finset.range (m + 1), C j,
    by
      have := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun j _ ↦ (hC j).le)
      linarith, ?_⟩
  intro f hf
  have hJ := frechetSobolevEnergy_nonneg (ball p.center p.radius) m f
  calc
    _ = ∑ j ∈ Finset.range (m + 1),
        ∫ x, ‖iteratedFDeriv ℝ j (p.extend Seeley.coeff f) x‖ ^ 2 := by
      simp only [frechetSobolevEnergy, iteratedFDerivWithin_univ, setIntegral_univ]
    _ ≤ ∑ j ∈ Finset.range (m + 1), C j * frechetSobolevEnergy (ball p.center p.radius) m f := by
      apply Finset.sum_le_sum
      intro j hj
      apply (hb j f hf).trans
      apply mul_le_mul_of_nonneg_left _ (hC j).le
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
      exact fun _ _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)
    _ = (∑ j ∈ Finset.range (m + 1), C j) * frechetSobolevEnergy (ball p.center p.radius) m f :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by nlinarith

end JanetCartan.BallExtension.Parameters
