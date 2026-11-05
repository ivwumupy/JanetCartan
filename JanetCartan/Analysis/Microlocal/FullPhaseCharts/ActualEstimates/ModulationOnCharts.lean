module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualQuotient
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Neighborhoods
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Basic

/-!
# The exact scalar quotient on the constructed chart boxes

The integral scalar modulation is identified with the nonzero divided phase
on the SAME boxes later used for the inverse maps. Its extension through zero
is the actual covector differential, as in
`app:ch_seed:eq:seed-exact-phase-quotient`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (n - 1)
local notation "X" => WithLp 2 (ℝ × E)

/-- The literal scalar modulation at zero equals the covector differential
on the same current phase (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem modulationPhase_current_zero (Q : _) (p : Euclidean 2) (u : ℝ × E) (x : X) :
    Comparison.modulationPhase (current T Q) (spatialCarrier T) 0 p u x =
      fderiv ℝ (fun ξ ↦ current T Q (x,ξ)) (spatialCarrier T (p,u.1)) u.2 := by
  simp only [Comparison.modulationPhase, phaseShiftQuotient_zero, inner_gradient_left]

/-- Choose the scalar quotient's epsilon cap before any current frame.
The geometric assumptions are exactly the radius and carrier-buffer outputs
of the actual inverse constructor. Scalar smoothness and the literal divided
phase identity are proved, not assumed
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_modulation_on_chart_boxes {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (ηb : E) :
    ∃ e₀ > (0 : ℝ), ∀ r s e : ℝ,
      0 < s → s ≤ r → r ≤ 1 / 4 → 2 * e < e₀ →
      3 * r < T.family.radius / 8 →
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) →
      ∀ Q,
        ContDiffOn ℝ ∞ (fun q : (ℝ × Euclidean 2 × X × X) × (ℝ × E) ↦
          Comparison.modulationPhase (current T Q) (spatialCarrier T)
            q.1.1 q.1.2.1 q.2 q.1.2.2.1)
          (fullParameterSet z₀ s (2 * e) ×ˢ dataSet z₀ ηb (2 * r)) ∧
        (∀ p ∈ fullParameterSet z₀ s (2 * e), ∀ u ∈ dataSet z₀ ηb (2 * r),
          p.1 ≠ 0 →
          Comparison.modulationPhase (current T Q) (spatialCarrier T)
            p.1 p.2.1 u p.2.2.1 =
          (current T Q (p.2.2.1, spatialCarrier T (p.2.1,u.1) + p.1 • u.2) -
            current T Q (p.2.2.1, spatialCarrier T (p.2.1,u.1))) / p.1) := by
  obtain ⟨e₀, he₀, hmod⟩ := exists_smooth_modulation T hP
    (show 0 < ‖ηb‖ + 1 by positivity)
  refine ⟨e₀, he₀, ?_⟩
  intro r s e hs hsr hr he hphys hcarrier Q
  let A := (fullParameterSet (n := n) z₀ s (2 * e) ×ˢ dataSet z₀ ηb (2 * r))
  let idx := fun q : (ℝ × Euclidean 2 × X × X) × (ℝ × E) ↦
    (((carrierParameters (q.1.2.1,q.2.1),q.2.2),q.1.1),q.1.2.2.1)
  have hi : ContDiff ℝ ∞ idx :=
    (((carrierParameters.contDiff.comp (contDiff_fst.snd.fst.prodMk contDiff_snd.fst)).prodMk
      contDiff_snd.snd).prodMk contDiff_fst.fst).prodMk contDiff_fst.snd.snd.fst
  have hmap : MapsTo idx A
      (((parameterInterior (3 * P.radius / 2) ×ˢ ball (0 : E) (‖ηb‖ + 1)) ×ˢ
        Ioo (-e₀) e₀) ×ˢ ball (0 : X) T.family.radius) := by
    intro q hq
    have hcr := hcarrier (show (q.1.2.1,q.2.1) ∈
        closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) from
      ⟨closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hq.1.2.1),
        closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hq.2.1)⟩)
    have hη : q.2.2 ∈ ball (0 : E) (‖ηb‖ + 1) := by
      rw [mem_ball, dist_zero_right]
      have hdist : ‖q.2.2 - ηb‖ < 2 * r := mem_ball_iff_norm.mp hq.2.2
      have hn := norm_le_insert' q.2.2 ηb
      linarith
    have hε : q.1.1 ∈ Ioo (-e₀) e₀ :=
      ⟨by linarith [hq.1.1.1], by linarith [hq.1.1.2]⟩
    have hx : q.1.2.2.1 ∈ ball (0 : X) T.family.radius :=
      ball_subset_ball (by linarith [T.family.radius_pos]) hq.1.2.2.1
    exact ⟨⟨⟨hcr,hη⟩,hε⟩,hx⟩
  refine ⟨(hmod Q).1.comp (f := idx) hi.contDiffOn hmap, ?_⟩
  intro p hp u hu hne
  have hm := hmap (show (p,u) ∈ A from ⟨hp,hu⟩)
  exact (hmod Q).2.1 _ hm.1.1 _ hm.1.2 hne _ hm.2

end JanetCartan.FullPhaseCharts.ActualEstimates
