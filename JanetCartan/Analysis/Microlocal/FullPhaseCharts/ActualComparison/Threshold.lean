module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Boxes
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison

/-!
# Primitive frame thresholds for the literal actual charts

This is the concrete instantiation of the comparison following
`app:ch_seed:eq:seed-quotient-integral`. All analytic hypotheses of `Comparison`
are discharged for `ActualPhase.current T Q` on the SAME constructed chart.
The remaining box conditions are fixed finite-dimensional geometry and are
produced by `exists_box_radius`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualComparison
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The three literal full-chart errors, including the joint derivative in
all spectator and physical variables (`app:ch_seed:prop:seed-phase-charts`).
This predicate is a conclusion of the concrete frame estimate below. -/
def FullChartComparison (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r ε τ : ℝ) : Prop :=
  ∀ q ∈ closedBall (spectatorCenter z₀) r ×ˢ
      ((closedBall (0 : WithLp 2 (ℝ × Euclidean (n - 1))) r ×ˢ closedBall 0 r) ×ˢ
        (closedBall (z₀ 0) r ×ˢ closedBall ηb r)),
    ‖Comparison.fullChart (current T Q) (spatialCarrier T) ε q.1 q.2.1.1 q.2.1.2 q.2.2 -
      frozenChart (fun z ↦ gradient (dispersion T) (spatialCarrier T (q.1,z))) q.2.2‖ < τ ∧
    ‖fderiv ℝ (fun a : Euclidean 2 ×
        (WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1))) ×
        (ℝ × Euclidean (n - 1)) ↦
        Comparison.fullChart (current T Q) (spatialCarrier T) ε
          a.1 a.2.1.1 a.2.1.2 a.2.2) q -
      fderiv ℝ (fun a : Euclidean 2 ×
        (WithLp 2 (ℝ × Euclidean (n - 1)) × WithLp 2 (ℝ × Euclidean (n - 1))) ×
        (ℝ × Euclidean (n - 1)) ↦
        frozenChart (fun z ↦ gradient (dispersion T) (spatialCarrier T (a.1,z))) a.2.2) q‖ < τ ∧
    ‖fderiv ℝ (Comparison.fullChart (current T Q) (spatialCarrier T) ε
        q.1 q.2.1.1 q.2.1.2) q.2.2 -
      fderiv ℝ (frozenChart (fun z ↦ gradient (dispersion T)
        (spatialCarrier T (q.1,z)))) q.2.2‖ < τ

/-- The literal transverse value and eta-derivative errors relative to the
identity (`app:ch_seed:prop:seed-phase-charts`). -/
def TransverseChartComparison (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r ε τ : ℝ) : Prop :=
  ∀ p ∈ closedBall (spectatorCenter z₀) r, ∀ t : ℝ, ∀ y y' : Euclidean (n - 1),
    WithLp.toLp 2 (t,y) ∈ closedBall 0 r → WithLp.toLp 2 (t,y') ∈ closedBall 0 r →
    ∀ z ∈ closedBall (z₀ 0) r, ∀ η ∈ closedBall ηb r,
    ‖Comparison.transverseChart (current T Q) (spatialCarrier T) ε p t y y' (z,η) - η‖ < τ ∧
    ‖fderiv ℝ (fun v ↦ Comparison.transverseChart (current T Q) (spatialCarrier T)
        ε p t y y' (z,v)) η - ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ < τ

/-- Concrete comparison on a fixed compact box. The phase error is obtained
at order four from `exists_current_comparison_threshold`, using monotonicity
from primitive frame order six. No phase or chart error is assumed
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_frame_comparison_threshold {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) {r : ℝ}
    (hr : r < T.family.radius / 8)
    (hbox : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > (0 : ℝ), ∃ εStar > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ ε, |ε| ≤ εStar →
        FullChartComparison T Q z₀ ηb r ε τ ∧ TransverseChartComparison T Q z₀ ηb r ε τ := by
  let M := ‖ηb‖ + |r| + 1
  have hM : 0 < M := by dsimp [M]; positivity
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
  have hη (η : Euclidean (n - 1)) (hη : η ∈ closedBall ηb r) : η ∈ ball 0 M := by
    rw [mem_ball, dist_zero_right]
    calc
      ‖η‖ ≤ ‖η - ηb‖ + ‖ηb‖ := by simpa only [add_comm] using norm_le_insert' η ηb
      _ ≤ r + ‖ηb‖ := add_le_add (by simpa [dist_eq_norm] using hη) le_rfl
      _ < M := by dsimp [M]; linarith [le_abs_self r]
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hRshift (q : Euclidean 2 × (ℝ × Euclidean (n - 1))) (hq : q ∈ R)
      (ε : ℝ) (hε : |ε| ≤ e) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) :
      spatialCarrier T (q.1,q.2.1) + (s * ε) • q.2.2 ∈
        ball (covectorCenter T) T.family.radius :=
    hshift _ (fun i ↦ (hq.1 i).le) _ (by simpa using (mem_ball.mp hq.2).le) ε hε s hs
  have hQR : closedBall (spectatorCenter z₀) r ×ˢ
      (closedBall (z₀ 0) r ×ˢ closedBall ηb r) ⊆ R :=
    fun q hq ↦ ⟨hbox ⟨hq.1, hq.2.1⟩, hη _ hq.2.2⟩
  have hsmall : T.family.radius < 2 * T.family.radius := by linarith [T.family.radius_pos]
  obtain ⟨d, hd, εStar, hstar, _, hcompare⟩ := Comparison.exists_phaseCharts_c1_comparison
    (H := dispersion T) (ζ := spatialCarrier T)
    (P₀ := closedBall (spectatorCenter z₀) r) (B := closedBall 0 r)
    (I := closedBall (z₀ 0) r) (J := closedBall ηb r)
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
  refine ⟨δ, hδ, εStar, hstar, fun Q hQ ε hε ↦ ?_⟩
  exact hcompare (current T Q) (current_smooth T Q)
    (hphase Q ((cNorm_mono_order (by norm_num : 4 + 1 ≤ 6)).trans_lt hQ) _ Subset.rfl) ε hε

end JanetCartan.FullPhaseCharts.ActualComparison
