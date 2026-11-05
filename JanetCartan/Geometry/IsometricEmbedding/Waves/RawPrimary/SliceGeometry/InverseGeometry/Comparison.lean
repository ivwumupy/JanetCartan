module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Geometry
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Threshold

/-!
# Comparison on the complete normalized slice band

The input radius is independent of the physical and carrier radii. This supplies
`exists_slice_inverse_geometry` with the actual value and derivative comparison
on the full radius-three input ball, from original state-ball frame closeness.
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

/-- A physical/carrier comparison radius exists even on the boundary of the
original compact cube. The middle carrier neighborhood supplies the open buffer
required by `exists_slice_inverse_geometry`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_slice_comparison_radius {c C : ℝ} (hP : P.IsValid c C)
    {z : Euclidean 3} (hz : z ∈ parameterCube P.radius) :
    ∃ r > (0 : ℝ), r < T.family.radius / 8 ∧
      closedBall (spectatorCenter z) r ×ˢ closedBall (z 0) r ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) := by
  have hO : IsOpen (carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    (isOpen_parameterInterior _).preimage carrierParameters.continuous
  have hz' : (spectatorCenter z, z 0) ∈
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) := by
    simpa only [mem_preimage, carrierParameters_spectatorCenter] using
      (middle_parameter_buffers hP).1 hz
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hz')
  let r := min (d / 2) (T.family.radius / 16)
  have hr : 0 < r := lt_min (by positivity) (by have := T.family.radius_pos; positivity)
  refine ⟨r, hr, ?_, ?_⟩
  · have := min_le_right (d / 2) (T.family.radius / 16)
    dsimp only [r]; linarith [T.family.radius_pos]
  · intro q hq
    apply hsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    have hrd : r < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact ⟨(mem_closedBall.mp hq.1).trans_lt hrd,
      (mem_closedBall.mp hq.2).trans_lt hrd⟩

/-- The actual transverse chart is uniformly close to the identity throughout
the complete radius-three eta ball. The eta ball does not shrink with `r`.
This discharges the comparison inputs of `exists_slice_inverse_geometry`
from the SAME current phase and primitive frame threshold
(`app:ch_seed:prop:seed-phase-charts`, `app:ch_waves:setup:oscillatory`). -/
theorem exists_slice_transverse_comparison {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r : ℝ} (hr : r < T.family.radius / 8)
    (hbox : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ transverseParameterSet z₀ r e, ∀ η ∈ closedBall (0 : Euclidean (n - 1)) 3,
        ‖transverseChartFamily (current T Q) (spatialCarrier T) p η - η‖ < τ ∧
        ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
          ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ < τ := by
  let M : ℝ := 5
  have hM : 0 < M := by norm_num [M]
  obtain ⟨e, he, hshift⟩ := exists_covector_shift_buffer T hP hM
  let V := carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)
  let R : Set (Euclidean 2 × (ℝ × Euclidean (n - 1))) :=
    {q | (q.1, q.2.1) ∈ V ∧ q.2.2 ∈ ball 0 M}
  let B : Set (WithLp 2 (ℝ × Euclidean (n - 1))) := ball 0 (T.family.radius / 8)
  let A : Set (Euclidean 2 ×
      (WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1))) ×
      (ℝ × Euclidean (n - 1))) :=
    {q | (q.1, q.2.2) ∈ R ∧ q.2.1.1 ∈ B ∧ q.2.1.2 ∈ B}
  have hV : IsOpen V := (isOpen_parameterInterior _).preimage carrierParameters.continuous
  have hR : IsOpen R := (hV.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop))
  have hA : IsOpen A := (hR.preimage (by fun_prop)).inter
    ((isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop)))
  have hmid : V ⊆ carrierParameters ⁻¹' parameterInterior (2 * P.radius) :=
    fun q hq ↦ (middle_parameter_buffers hP).2 (fun i ↦ (hq i).le)
  have hζ := (spatialCarrier_smooth T hP).mono hmid
  have hη (η : Euclidean (n - 1)) (hη : η ∈ closedBall 0 3) : η ∈ ball 0 M :=
    closedBall_subset_ball (by norm_num [M]) hη
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hRshift (q : Euclidean 2 × (ℝ × Euclidean (n - 1))) (hq : q ∈ R)
      (ε : ℝ) (hε : |ε| ≤ e) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) :
      spatialCarrier T (q.1,q.2.1) + (s * ε) • q.2.2 ∈
        ball (covectorCenter T) T.family.radius :=
    hshift _ (fun i ↦ (hq.1 i).le) _ (by simpa using (mem_ball.mp hq.2).le) ε hε s hs
  have hQR : closedBall (spectatorCenter z₀) r ×ˢ
      (closedBall (z₀ 0) r ×ˢ closedBall (0 : Euclidean (n - 1)) 3) ⊆ R :=
    fun q hq ↦ ⟨hbox ⟨hq.1, hq.2.1⟩, hη _ hq.2.2⟩
  have hsmall : T.family.radius < 2 * T.family.radius := by linarith [T.family.radius_pos]
  obtain ⟨d, hd, εStar, hstar, _, hcompare⟩ := Comparison.exists_phaseCharts_c1_comparison
    (H := dispersion T) (ζ := spatialCarrier T)
    (P₀ := closedBall (spectatorCenter z₀) r) (B := closedBall 0 r)
    (I := closedBall (z₀ 0) r) (J := closedBall (0 : Euclidean (n - 1)) 3)
    (V := V) (Ω := ball (0, covectorCenter T) (2 * T.family.radius))
    (K := closedBall (0, covectorCenter T) T.family.radius)
    (U := A) (T := ball 0 T.family.radius) (W := Ioo (-1 : ℝ) 2)
    (Ωξ := ball (covectorCenter T) (2 * T.family.radius)) (R := R) (L := Ioo (-e) e)
    (isCompact_closedBall _ _) (isCompact_closedBall _ _) (convex_closedBall _ _)
    (isCompact_closedBall _ _) (isCompact_closedBall _ _) hV hbox hζ
    (isCompact_closedBall _ _) (closedBall_subset_ball hsmall) isOpen_ball
    hA isOpen_ball isOpen_Ioo hIW
    (fun q hq ↦ ⟨hQR ⟨hq.1, hq.2.2⟩,
      closedBall_subset_ball hr hq.2.1.1, closedBall_subset_ball hr hq.2.1.2⟩)
    (fun q hq ↦ hq.1.1)
    (fun q hq s hs ↦ physical_segment_mem_phase_ball T
      (ball_subset_closedBall hq.2.1) (ball_subset_closedBall hq.2.2) hs)
    (half_pos he)
    (by
      intro ε hε q hq y hy s hs
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(mem_ball.mp hy).trans hsmall,
        (mem_ball.mp (hRshift _ hq.1 ε (hε.trans (by linarith)) s hs)).trans hsmall⟩)
    (by
      intro ε hε p hp x hx z hz η hη' s hs
      rw [mem_closedBall, Prod.dist_eq, max_le_iff]
      refine ⟨(mem_closedBall.mp hx).trans (by linarith [T.family.radius_pos]), ?_⟩
      exact (mem_ball.mp (hRshift (p,z,η) (hQR ⟨hp,hz,hη'⟩)
        ε (hε.trans (by linarith)) s (hIW hs))).le)
    isOpen_ball (fun q hq ↦ (mem_ball.mp hq).trans_le' (le_max_right _ _))
    (dispersion_smooth T) hR hQR (fun q hq ↦ hq.1) isOpen_Ioo
    (fun ε hε ↦ abs_lt.mp (hε.trans_lt (half_lt_self he)))
    (fun q hq ε hε s hs ↦ ball_subset_ball hsmall.le
      (hRshift q hq ε ((abs_lt.mpr hε).le) s hs)) hτ
  obtain ⟨δ, hδ, hphase⟩ := exists_current_comparison_threshold T 4 hd
  refine ⟨δ, hδ, εStar, hstar, fun Q hQ p hp η hη ↦ ?_⟩
  have hc := (hcompare (current T Q) (current_smooth T Q)
    (hphase Q ((cNorm_mono_order (by norm_num : 4 + 1 ≤ 6)).trans_lt hQ) _ Subset.rfl) p.1 (abs_lt.mpr hp.1).le).2
  exact hc p.2.1 (ball_subset_closedBall hp.2.1)
    p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
    (ball_subset_closedBall hp.2.2.2.1) (ball_subset_closedBall hp.2.2.2.2)
    p.2.2.2.1 (ball_subset_closedBall hp.2.2.1) η hη

end JanetCartan.RawPrimary.SliceGeometry
