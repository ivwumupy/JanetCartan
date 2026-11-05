module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualComparison
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence

/-!
# Freezing the spectator coordinates on a common data chart

The common inverse in `app:ch_seed:prop:seed-phase-charts` must use one
reference map. Compact continuity of its actual value and data differential
allows the spectator box to shrink after the inverse's value tolerance is
chosen, without changing the data chart or the Hamilton phase.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.FullPhaseCharts.ActualInverses
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase
open ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Joint regularity of the frozen chart on the literal carrier interior,
used to freeze spectators in `app:ch_seed:prop:seed-phase-charts`. -/
theorem frozenChart_contDiffAt {c C : ℝ} (hP : P.IsValid c C)
    {q : Euclidean 2 × (ℝ × Euclidean (n - 1))}
    (hq : carrierParameters (q.1, q.2.1) ∈ parameterInterior (2 * P.radius)) :
    ContDiffAt ℝ ∞ (fun a : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
      frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (a.1,t))) a.2) q := by
  have hv := (FrozenIncidence.carrier_gradient_smooth T hP).contDiffAt
    (((isOpen_parameterInterior _).preimage carrierParameters.continuous).mem_nhds hq)
  exact ((hv.comp q (contDiffAt_fst.prodMk contDiffAt_snd.fst)).inner ℝ
    contDiffAt_snd.snd).prodMk contDiffAt_snd.snd

/-- Uniform value and data-derivative variation of the ACTUAL frozen map.
Only fixed carrier-domain containment is required. In the common inverse
assembly the data radius is fixed first and the spectator radius is chosen
after the buffered-image tolerance (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_frozen_spectator_radius {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) {r : ℝ} (hr : 0 < r)
    (hcarrier : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (2 * P.radius))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ s > 0, s ≤ r ∧ ∀ p ∈ closedBall (spectatorCenter z₀) s,
      ∀ u ∈ dataBox z₀ ηb r,
        ‖frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (p,t))) u -
          frozenChart (fun t ↦ gradient (dispersion T)
            (spatialCarrier T (spectatorCenter z₀,t))) u‖ < τ ∧
        ‖fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
            (spatialCarrier T (p,t)))) u -
          fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
            (spatialCarrier T (spectatorCenter z₀,t)))) u‖ < τ := by
  let J := closedBall (spectatorCenter z₀) r ×ˢ dataBox z₀ ηb r
  let jet := fun q : Euclidean 2 × (ℝ × Euclidean (n - 1)) ↦
    (frozenChart (fun t ↦ gradient (dispersion T) (spatialCarrier T (q.1,t))) q.2,
      fderiv ℝ (frozenChart (fun t ↦ gradient (dispersion T)
        (spatialCarrier T (q.1,t)))) q.2)
  have hJ : IsCompact J := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn jet J := by
    intro q hq
    have hq' : carrierParameters (q.1,q.2.1) ∈ parameterInterior (2 * P.radius) :=
      hcarrier (show (q.1,q.2.1) ∈ closedBall (spectatorCenter z₀) r ×ˢ
        closedBall (z₀ 0) r from ⟨hq.1,hq.2.1⟩)
    exact ((frozenChart_contDiffAt T hP (q := q) hq').continuousAt.prodMk
      (FrozenIncidence.frozen_data_derivative_continuousAt T hP (q := q) hq')).continuousWithinAt
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hJ.uniformContinuousOn_of_continuous hc) τ hτ
  refine ⟨min r (d / 2), lt_min hr (by positivity), min_le_left _ _, ?_⟩
  intro p hp u hu
  have hp' := closedBall_subset_closedBall (min_le_left r (d / 2)) hp
  have hdist : dist (p,u) (spectatorCenter z₀,u) < d := by
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact (mem_closedBall.mp hp).trans_lt ((min_le_right r (d / 2)).trans_lt (by linarith))
  have h := hclose (p,u) (show (p,u) ∈ J from ⟨hp',hu⟩)
    (spectatorCenter z₀,u) (show (spectatorCenter z₀,u) ∈ J from
      ⟨mem_closedBall_self hr.le,hu⟩) hdist
  simpa only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
    max_lt_iff] using h

end JanetCartan.FullPhaseCharts.ActualInverses
