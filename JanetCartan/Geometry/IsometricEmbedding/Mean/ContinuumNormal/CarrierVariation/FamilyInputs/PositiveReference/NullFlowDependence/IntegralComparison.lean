module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.TimeIntegral
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Difference of the actual characteristic integrals

The compact cylinder stays inside the original time and label buffers. This
supplies the integral step of the scalar comparison in
`app:ch_background:prop:bg-frame`, using the formula of
`app:ch_waves:thm:leading`. Both orientations of time are retained.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open NullTransport.AmplitudeTame FullPhaseCharts.InverseEstimates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a fixed compact subset of the original characteristic cylinder, the
literal integral has a linear difference bound with no derivative loss.
The larger compact cylinder and constant precede both coefficients. Consumed
by `exists_cNorm_characteristicTransport_sub_lt`
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`). -/
theorem exists_cNorm_timeIntegral_sub_le
    {p : E} {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    {K : Set (ℝ × E)} (hK : IsCompact K)
    (hKW : K ⊆ Ioo (-τ) τ ×ˢ ball p r) (m : ℕ) :
    ∃ L : Set (ℝ × E), IsCompact L ∧ L ⊆ Ioo (-τ) τ ×ˢ ball p r ∧
      ∃ C > 0, ∀ c c₀ : ℝ × E → ℝ,
        ContDiffOn ℝ ∞ c (Ioo (-τ) τ ×ˢ ball p r) →
        ContDiffOn ℝ ∞ c₀ (Ioo (-τ) τ ×ˢ ball p r) →
        cNorm K m ((fun q ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) -
          (fun q ↦ ∫ s in (0 : ℝ)..q.1, c₀ (s, q.2))) ≤ C * cNorm L m (c - c₀) := by
  obtain ⟨a, ha, hKa⟩ := exists_pos_lt_subset_ball hτ
    (hK.image continuous_fst).isClosed (show Prod.fst '' K ⊆ ball (0 : ℝ) τ by
      rintro _ ⟨q, hq, rfl⟩
      simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using (hKW hq).1)
  obtain ⟨b, hb, hKb⟩ := exists_pos_lt_subset_ball hr
    (hK.image continuous_snd).isClosed (image_subset_iff.mpr fun _ hq ↦ (hKW hq).2)
  let W := Ioo (-τ) τ ×ˢ ball p r
  let O := Ioo (-a) a ×ˢ ball p b
  let L := Icc (-a) a ×ˢ closedBall p b
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_ball
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_ball
  have hL : IsCompact L := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKO : K ⊆ O := fun q hq ↦ ⟨by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hKa (mem_image_of_mem _ hq),
    hKb (mem_image_of_mem _ hq)⟩
  have hOL : O ⊆ L := prod_mono Ioo_subset_Icc_self ball_subset_closedBall
  have hLW : L ⊆ W := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨by linarith [ht.1, ha.2], by linarith [ht.2, ha.2]⟩,
      closedBall_subset_ball hb.2 hx⟩
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (q : ℝ × E) (hq : q ∈ O) :
      timeSegment s q ∈ L := by
    refine ⟨?_, ball_subset_closedBall hq.2⟩
    change -a ≤ s * q.1 ∧ s * q.1 ≤ a
    have ht : |q.1| < a := abs_lt.mpr hq.1
    have hab : |s * q.1| ≤ a := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hs.2).trans ht.le
    exact abs_le.mp hab
  let B := ContinuousLinearMap.mul ℝ ℝ
  let A : ℝ := ∑ j ∈ Finset.range (m + 1), ‖B‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)
  let T := cNorm K m (Prod.fst : ℝ × E → ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := cNorm_nonneg _ _ _
  have hbound (c : ℝ × E → ℝ) (hc : ContDiffOn ℝ ∞ c W) :
      cNorm K m (fun q ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) ≤
        (1 + A * T * (m + 1)) * cNorm L m c := by
    let H : ℝ × (ℝ × E) → ℝ := fun z ↦ c (z.1 * z.2.1, z.2.2)
    have hH : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ O, ContDiffAt ℝ ∞ H z := by
      intro z hz
      exact (hc.contDiffAt (hW.mem_nhds (hLW (hseg z.1 hz.1 z.2 hz.2)))).comp z
        ((contDiffAt_fst.mul contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
    have hj (j : ℕ) (hj : j ≤ m) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
        (q : ℝ × E) (hq : q ∈ O) :
        ‖iteratedFDeriv ℝ j (fun x ↦ H (s, x)) q‖ ≤ cNorm L m c := by
      apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
        (timeSegment s) hW hc (hLW (hseg s hs q hq)) j).trans
      apply (mul_le_mul
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
          (fun w hw ↦ (hc.contDiffAt (hW.mem_nhds (hLW hw))).of_le (by simp))
          (hseg s hs q hq) hj)
        (pow_le_one₀ (norm_nonneg _) (norm_timeSegment_le hs))
        (pow_nonneg (norm_nonneg _) _) (cNorm_nonneg _ _ _)).trans_eq
      exact mul_one _
    have havg : cNorm K m (fun q ↦ ∫ s in (0 : ℝ)..1, H (s, q)) ≤
        (m + 1 : ℝ) * cNorm L m c := by
      simpa using cNorm_le_sum_of_bounds (fun _ _ ↦ cNorm_nonneg L m c)
        (fun j hj' q hq ↦ NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le hO hH
          (fun i hi ↦ hj i (hi.trans hj')) (hKO hq))
    have hsmooth := contDiffOn_fixedIntervalIntegral hO
      (F := H) (a := (0 : ℝ)) (b := 1) (by simpa using hH)
    have he : (fun q : ℝ × E ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) =
        (fun q ↦ B q.1 (∫ s in (0 : ℝ)..1, H (s, q))) :=
      funext (timeIntegral_eq_time_mul_average c)
    rw [he]
    apply (cNorm_bilinear_le_on B hK hO hKO contDiffOn_fst hsmooth m).trans
    change A * T * cNorm K m (fun q ↦ ∫ s in (0 : ℝ)..1, H (s, q)) ≤ _
    apply (mul_le_mul_of_nonneg_left havg (mul_nonneg hA hT)).trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (cNorm_nonneg _ _ _)
  refine ⟨L, hL, hLW, 1 + A * T * (m + 1), by positivity, ?_⟩
  intro c c₀ hc hc₀
  have he : cNorm K m ((fun q ↦ ∫ s in (0 : ℝ)..q.1, c (s, q.2)) -
      (fun q ↦ ∫ s in (0 : ℝ)..q.1, c₀ (s, q.2))) =
      cNorm K m (fun q ↦ ∫ s in (0 : ℝ)..q.1, (c - c₀) (s, q.2)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro q hq
    filter_upwards [hW.mem_nhds (hKW hq)] with x hx
    have hint (f : ℝ × E → ℝ) (hf : ContDiffOn ℝ ∞ f W) :
        IntervalIntegrable (fun s ↦ f (s, x.2)) MeasureTheory.volume 0 x.1 := by
      apply ContinuousOn.intervalIntegrable
      exact hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs ↦ ⟨ordConnected_Ioo.uIcc_subset ⟨neg_neg_of_pos hτ, hτ⟩ hx.1 hs, hx.2⟩)
    exact (intervalIntegral.integral_sub (hint c hc) (hint c₀ hc₀)).symm
  rw [he]
  exact hbound (c - c₀) (hc.sub hc₀)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
