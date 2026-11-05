module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualQuotient
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.TransverseProjection

/-!
# Joint smoothness of the actual chart families

The smooth modulation constructed in `ActualQuotient` is regrouped into the
literal families consumed by `InverseFamily`. The transverse identification
is proved using the actual phase's covector and physical segment buffers.
All domains are open, with both signs of epsilon, as required by
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualComparison
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual joint smoothness, including epsilon zero, on open full/transverse
parameter and data neighborhoods. The first conclusion is the Hilbert-space
averaged-gradient input expected by `exists_fullChart_inverseFamily`; the
other two are the literal chart families
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_smooth_chartFamilies {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) {r : ℝ}
    (hr : r ≤ T.family.radius / 8)
    (hbox : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ e > (0 : ℝ), ∀ Q,
      ContDiffOn ℝ ∞ (fun q :
        (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
          WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
        Comparison.modulationChart (current T Q) (spatialCarrier T)
          q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
        (fullParameterSet z₀ r e ×ˢ dataSet z₀ ηb r) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
        (fullParameterSet z₀ r e ×ˢ dataSet z₀ ηb r) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
        (transverseParameterSet z₀ r e ×ˢ ball ηb r) := by
  let M := ‖ηb‖ + |r| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨e₁, he₁, hmod⟩ := exists_smooth_modulation T hP hM
  obtain ⟨e₂, he₂, hshift⟩ := exists_covector_shift_buffer T hP hM
  let e := min e₁ e₂
  have he : 0 < e := lt_min he₁ he₂
  have hη (η : Euclidean (n - 1)) (hη : η ∈ ball ηb r) : η ∈ ball 0 M := by
    rw [mem_ball, dist_zero_right]
    calc
      ‖η‖ ≤ ‖η - ηb‖ + ‖ηb‖ := by simpa only [add_comm] using norm_le_insert' η ηb
      _ < r + ‖ηb‖ := add_lt_add_of_lt_of_le (by simpa [dist_eq_norm] using hη) le_rfl
      _ < M := by dsimp [M]; linarith [le_abs_self r]
  have hpoint {p : Euclidean 2} {z : ℝ}
      (hp : p ∈ ball (spectatorCenter z₀) r) (hz : z ∈ ball (z₀ 0) r) :
      carrierParameters (p,z) ∈ parameterInterior (3 * P.radius / 2) :=
    hbox ⟨ball_subset_closedBall hp, ball_subset_closedBall hz⟩
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsmall : T.family.radius < 2 * T.family.radius := by linarith [T.family.radius_pos]
  refine ⟨e, he, fun Q ↦ ?_⟩
  have havg := (hmod Q).2.2.1
  have hfull : ContDiffOn ℝ ∞ (fun q :
      (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
        WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
      Comparison.modulationChart (current T Q) (spatialCarrier T)
        q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      (fullParameterSet z₀ r e ×ˢ dataSet z₀ ηb r) := by
    apply havg.comp (f := fun q :
      (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
        WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
      (((carrierParameters (q.1.2.1, q.2.1), q.2.2), q.1.1), q.1.2.2.1, q.1.2.2.2))
      (by fun_prop)
    intro q hq
    exact ⟨⟨⟨hpoint hq.1.2.1 hq.2.1, hη _ hq.2.2⟩,
      abs_lt.mp ((abs_lt.mpr hq.1.1).trans_le (min_le_left _ _))⟩,
      ball_subset_ball hr hq.1.2.2.1, ball_subset_ball hr hq.1.2.2.2⟩
  have hf : ContDiffOn ℝ ∞
      (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
      (fullParameterSet z₀ r e ×ˢ dataSet z₀ ηb r) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1))).contDiff.comp_contDiffOn hfull
  refine ⟨hfull, hf, ?_⟩
  have hto : ContDiff ℝ ∞ (WithLp.toLp 2 : (ℝ × Euclidean (n - 1)) →
      WithLp 2 (ℝ × Euclidean (n - 1))) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1))).symm.contDiff
  have hproj : ContDiffOn ℝ ∞ (fun q :
      (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
        Euclidean (n - 1) ↦
      (fullChartFamily (current T Q) (spatialCarrier T)
        (q.1.1, q.1.2.1, WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.1),
          WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.2)) (q.1.2.2.2.1, q.2)).2)
      (transverseParameterSet z₀ r e ×ˢ ball ηb r) := by
    apply ContDiffOn.snd
    apply hf.comp (f := fun q :
      (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
        Euclidean (n - 1) ↦
      ((q.1.1, q.1.2.1, WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.1),
        WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.2)), (q.1.2.2.2.1, q.2))) (by fun_prop)
    intro q hq
    exact ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2⟩, hq.1.2.2.1, hq.2⟩
  apply hproj.congr
  intro q hq
  apply Comparison.transverseChart_eq_fullChart_snd
    (D := dataSet z₀ ηb r) (B := ball 0 T.family.radius)
    (Ω := ball (0, covectorCenter T) (2 * T.family.radius)) (W := Ioo (-1 : ℝ) 2)
    (isOpen_dataSet _ _ _) isOpen_ball isOpen_ball isOpen_Ioo hIW (current_smooth T Q)
  · apply (spatialCarrier_smooth T hP).comp (contDiffOn_const.prodMk contDiffOn_fst)
    intro u hu
    exact (middle_parameter_buffers hP).2 (fun i ↦ (hpoint hq.1.2.1 hu.1 i).le)
  · intro u hu x hx s hs
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨(mem_ball.mp hx).trans hsmall, ?_⟩
    exact (mem_ball.mp (hshift _ (fun i ↦ (hpoint hq.1.2.1 hu.1 i).le) _
      (by simpa using (mem_ball.mp (hη _ hu.2)).le) q.1.1
      ((abs_lt.mpr hq.1.1).le.trans (min_le_right _ _)) s hs)).trans hsmall
  · intro s hs
    have hid : WithLp.toLp 2 (q.1.2.2.1,
        q.1.2.2.2.2.2 + s • (q.1.2.2.2.2.1 - q.1.2.2.2.2.2)) =
        WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.2) +
          s • (WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.1) -
            WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.2)) := by
      apply WithLp.ofLp_injective
      simp
    rw [hid]
    exact physical_segment_mem_phase_ball T
      (closedBall_subset_closedBall hr (ball_subset_closedBall hq.1.2.2.2.1))
      (closedBall_subset_closedBall hr (ball_subset_closedBall hq.1.2.2.2.2)) (hIW hs)
  · exact ⟨hq.1.2.2.1, hq.2⟩

end JanetCartan.FullPhaseCharts.ActualComparison
