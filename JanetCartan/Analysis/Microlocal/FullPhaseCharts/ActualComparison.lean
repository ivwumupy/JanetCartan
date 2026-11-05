module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Neighborhoods
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Threshold
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison.Smoothness

/-!
# Actual full and transverse chart comparison

This discharges the concrete comparison paragraph following
`app:ch_seed:eq:seed-quotient-integral` for the SAME Hamilton chart retained by
`PatchQuantitativeFamily.currentChart`. The reference is the actual frozen
dispersion, whose affine phase identity is used by
`ActualPhase.exists_current_comparison_threshold`.

First choose a positive box radius and a two-sided smoothness interval using
only fixed geometry. Every smaller positive box is allowed. Then, for each
tolerance, choose the primitive frame threshold and epsilon threshold before
choosing the current frame. Comparison holds on the double-radius compact
boxes, hence on open parameter neighborhoods of the original closed boxes.
Smoothness holds on the triple-radius open boxes and past both epsilon
endpoints. `fullChartComparison_on_open_parameters` and its transverse
counterpart expose exactly the value/data-derivative inputs to `InverseFamily`.

The parent construction still chooses incidence and annulus tolerances and
assembles common inverses and their tame estimates. None of these conclusions
is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualComparison
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual comparison and joint smoothness on fixed, arbitrarily shrinkable
boxes (`app:ch_seed:prop:seed-phase-charts`). Radius `ρ` is the closed core,
`2 * ρ` is the compact comparison buffer, and `3 * ρ` is the open smoothness
extension. The open epsilon interval of radius `2 * εStar` contains the
closed interval `[-εStar, εStar]`, including both endpoints and zero.
Only primitive whole-frame `C⁶` closeness is an analytic premise. -/
theorem exists_actual_chart_comparison {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (ηb : Euclidean (n - 1)) :
    ∃ ρ₀ > (0 : ℝ), ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
      3 * ρ < T.family.radius / 8 ∧
      (closedBall (spectatorCenter z₀) (3 * ρ) ×ˢ closedBall (z₀ 0) (3 * ρ) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
      ∃ e > (0 : ℝ),
        (∀ Q,
          ContDiffOn ℝ ∞ (fun q :
            (ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean (n - 1)) ×
              WithLp 2 (ℝ × Euclidean (n - 1))) × (ℝ × Euclidean (n - 1)) ↦
            Comparison.modulationChart (current T Q) (spatialCarrier T)
              q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
            (fullParameterSet z₀ (3 * ρ) e ×ˢ dataSet z₀ ηb (3 * ρ)) ∧
          ContDiffOn ℝ ∞ (Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T)))
            (fullParameterSet z₀ (3 * ρ) e ×ˢ dataSet z₀ ηb (3 * ρ)) ∧
          ContDiffOn ℝ ∞ (Function.uncurry (transverseChartFamily (current T Q) (spatialCarrier T)))
            (transverseParameterSet z₀ (3 * ρ) e ×ˢ ball ηb (3 * ρ))) ∧
        ∀ τ, 0 < τ → ∃ δ > (0 : ℝ), ∃ εStar > (0 : ℝ), 2 * εStar < e ∧
          ∀ Q,
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q.1 - fun _ ↦ cubeStress n) < δ →
            ∀ ε, |ε| ≤ 2 * εStar →
              FullChartComparison T Q z₀ ηb (2 * ρ) ε τ ∧
              TransverseChartComparison T Q z₀ ηb (2 * ρ) ε τ := by
  obtain ⟨ρ₀, hρ₀, hboxes⟩ := exists_box_radius T hP hz₀
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρmax ↦ ?_⟩
  obtain ⟨_, hphys, hcarrier⟩ := hboxes ρ hρ hρmax
  obtain ⟨e, he, hsmooth⟩ := exists_smooth_chartFamilies T hP z₀ ηb hphys.le hcarrier
  refine ⟨hphys, hcarrier, e, he, hsmooth, fun τ hτ ↦ ?_⟩
  have h₂₃ : 2 * ρ ≤ 3 * ρ := by linarith
  have hcarrier₂ : closedBall (spectatorCenter z₀) (2 * ρ) ×ˢ
      closedBall (z₀ 0) (2 * ρ) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun q hq ↦ hcarrier ⟨closedBall_subset_closedBall h₂₃ hq.1,
      closedBall_subset_closedBall h₂₃ hq.2⟩
  obtain ⟨δ, hδ, ec, hec, hcomp⟩ := exists_frame_comparison_threshold T hP z₀ ηb
    (h₂₃.trans_lt hphys) hcarrier₂ hτ
  let εStar := min e ec / 4
  have hstar : 0 < εStar := div_pos (lt_min he hec) (by norm_num)
  have hstar_e : 2 * εStar < e := by dsimp [εStar]; linarith [min_le_left e ec]
  have hstar_c : 2 * εStar ≤ ec := by dsimp [εStar]; linarith [min_le_right e ec]
  exact ⟨δ, hδ, εStar, hstar, hstar_e,
    fun Q hQ ε hε ↦ hcomp Q hQ ε (hε.trans hstar_c)⟩

/-- The actual full comparison on a larger compact box gives the open
parameter comparison required by `exists_fullChart_inverseFamily`. The
frozen velocity is exactly the gradient of the constructed dispersion
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem fullChartComparison_on_open_parameters (Q : _) {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} {r e τ : ℝ}
    (h : ∀ ε, |ε| ≤ e → FullChartComparison T Q z₀ ηb r ε τ) :
    ∀ p ∈ fullParameterSet z₀ r e,
      ∀ u ∈ closedBall (z₀ 0) r ×ˢ closedBall ηb r,
      ‖fullChartFamily (current T Q) (spatialCarrier T) p u -
        frozenChart (fun z ↦ gradient (dispersion T) (spatialCarrier T (p.2.1,z))) u‖ < τ ∧
      ‖fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) u -
        fderiv ℝ (frozenChart (fun z ↦ gradient (dispersion T)
          (spatialCarrier T (p.2.1,z)))) u‖ < τ := by
  intro p hp u hu
  have hc := h p.1 (abs_lt.mpr hp.1).le (p.2.1, (p.2.2.1,p.2.2.2), u)
    ⟨ball_subset_closedBall hp.2.1,
      ⟨ball_subset_closedBall hp.2.2.1, ball_subset_closedBall hp.2.2.2⟩, hu⟩
  exact ⟨hc.1, hc.2.2⟩

/-- The actual transverse comparison on an open parameter neighborhood,
with the literal eta derivative expected by `exists_transverseChart_inverseFamily`
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem transverseChartComparison_on_open_parameters (Q : _) {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} {r e τ : ℝ}
    (h : ∀ ε, |ε| ≤ e → TransverseChartComparison T Q z₀ ηb r ε τ) :
    ∀ p ∈ transverseParameterSet z₀ r e, ∀ η ∈ closedBall ηb r,
      ‖transverseChartFamily (current T Q) (spatialCarrier T) p η - η‖ < τ ∧
      ‖fderiv ℝ (transverseChartFamily (current T Q) (spatialCarrier T) p) η -
        ContinuousLinearMap.id ℝ (Euclidean (n - 1))‖ < τ := by
  intro p hp η hη
  exact h p.1 (abs_lt.mpr hp.1).le p.2.1 (ball_subset_closedBall hp.2.1)
    p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
    (ball_subset_closedBall hp.2.2.2.1) (ball_subset_closedBall hp.2.2.2.2)
    p.2.2.2.1 (ball_subset_closedBall hp.2.2.1) η hη

end JanetCartan.FullPhaseCharts.ActualComparison
