module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Domains
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Smoothness

/-!
# Smooth extension of the entire transverse input band

The physical and carrier radius is small, while eta ranges independently over
the radius-four ball. `exists_slice_inverse_geometry` uses this open extension
of the closed radius-three inverse domain. Every phase is the retained current
Hamilton phase, and the epsilon interval crosses zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual joint smoothness with the whole radius-four eta extension retained,
independently of the physical radius. This supplies the regularity input to
`exists_slice_inverse_geometry` before the current frame is chosen
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_slice_transverse_smooth {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r : ℝ} (hr : r ≤ T.family.radius / 8)
    (hbox : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ e > (0 : ℝ), ∀ Q,
      ContDiffOn ℝ ∞
        (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
        (transverseParameterSet z₀ r e ×ˢ sliceInputExtension n) := by
  let M : ℝ := 5
  have hM : 0 < M := by norm_num [M]
  obtain ⟨e₁, he₁, hmod⟩ := exists_smooth_modulation T hP hM
  obtain ⟨e₂, he₂, hshift⟩ := exists_covector_shift_buffer T hP hM
  let e := min e₁ e₂
  have he : 0 < e := lt_min he₁ he₂
  have hη (η : Euclidean (n - 1)) (hη : η ∈ ball 0 4) : η ∈ ball 0 M :=
    ball_subset_ball (by norm_num [M]) hη
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
      (fullParameterSet z₀ r e ×ˢ (ball (z₀ 0) r ×ˢ ball (0 : Euclidean (n - 1)) 4)) := by
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
      (fullParameterSet z₀ r e ×ˢ (ball (z₀ 0) r ×ˢ ball (0 : Euclidean (n - 1)) 4)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1))).contDiff.comp_contDiffOn hfull
  have hto : ContDiff ℝ ∞ (WithLp.toLp 2 : (ℝ × Euclidean (n - 1)) →
      WithLp 2 (ℝ × Euclidean (n - 1))) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean (n - 1))).symm.contDiff
  have hproj : ContDiffOn ℝ ∞ (fun q :
      (ℝ × Euclidean 2 × ℝ × ℝ × Euclidean (n - 1) × Euclidean (n - 1)) ×
        Euclidean (n - 1) ↦
      (fullChartFamily (current T Q) (spatialCarrier T)
        (q.1.1, q.1.2.1, WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.1),
          WithLp.toLp 2 (q.1.2.2.1, q.1.2.2.2.2.2)) (q.1.2.2.2.1, q.2)).2)
      (transverseParameterSet z₀ r e ×ˢ ball (0 : Euclidean (n - 1)) 4) := by
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
    (D := (ball (z₀ 0) r ×ˢ ball (0 : Euclidean (n - 1)) 4)) (B := ball 0 T.family.radius)
    (Ω := ball (0, covectorCenter T) (2 * T.family.radius)) (W := Ioo (-1 : ℝ) 2)
    (isOpen_ball.prod isOpen_ball) isOpen_ball isOpen_ball isOpen_Ioo hIW (current_smooth T Q)
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

end JanetCartan.RawPrimary.SliceGeometry
