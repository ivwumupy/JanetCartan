module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.HamiltonComparison.SectionFlowRegularity

/-!
# Smoothness of the original retained forward maps

The Hamilton ODE and its actual smooth initial section imply smoothness on
the original source ball. No replacement flow or reduced target is used.
This discharges the regularity input to the forward and inverse comparisons
for `app:lem:common-hamilton-phase`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius NNReal

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open HamiltonPhase ActualCarriers CurrentFullPhase FrozenMenu FrozenPhaseReference
open JanetCartan.ODE

variable {n : ℕ} {ξ : Euclidean n} {a : AdaptedSection ξ} {N : LocalFrozenReference a}
  {U : Set (Euclidean n)} {hU : IsOpen U}
  (L : LocalQuantitativeFamily N U hU)

/-- The initial section of the actual retained flow is smooth throughout its
original parameter ball. This is the initial regularity input of the original
forward comparison (`app:lem:common-hamilton-phase`). -/
theorem retained_initialState_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun s ↦ ((L.flow Q).position (0, s), (L.flow Q).momentum (0, s)))
      (ball a.baseData (3 * L.sourceRadius)) := by
  have hadm (s) (hs : s ∈ ball a.baseData (3 * L.sourceRadius)) :
      (0, s) ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters := by
    apply L.source_admissible Q
    rw [mem_ball, Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hs
  have hp : ContDiffOn ℝ ∞ (fun s ↦ (L.flow Q).position (0, s))
      (ball a.baseData (3 * L.sourceRadius)) := by
    apply ((L.flow Q).sectionMap.contDiff.comp contDiff_fst).contDiffOn.congr
    intro s hs
    exact (L.flow Q).initial_position s (hadm s hs).2
  exact hp.prodMk ((L.momentum_smooth Q).comp
    (contDiffOn_const.prodMk contDiffOn_id) hadm)

variable (hdomain : ∀ z ∈ N.stateDomain, z.1 ∈ U)

include hdomain

set_option maxHeartbeats 600000 in
/-- Smoothness of the SAME retained state on the full original source ball.
The proof derives parameter Lipschitz bounds by Grönwall from the compact
state range and the actual initial section, then bootstraps its variational
equation. This discharges, rather than assumes, the smoothness required by
`exists_retained_joint_flow_tolerance` (`app:lem:common-hamilton-phase`). -/
theorem retained_state_smooth (Q : _) :
    ContDiffOn ℝ ∞ (fun q ↦ ((L.flow Q).position q, (L.flow Q).momentum q))
      (ball ((0 : ℝ), a.baseData) (3 * L.sourceRadius)) := by
  let H := normalizedHomogeneousSymbol hU Q.1 Q.2.1
  let T := 3 * L.sourceRadius
  let Ψ : InitialData (Euclidean (n - 1)) × ℝ → Euclidean n × Euclidean n :=
    fun q ↦ ((L.flow Q).position (q.2, q.1), (L.flow Q).momentum (q.2, q.1))
  let σ : InitialData (Euclidean (n - 1)) → Euclidean n × Euclidean n := fun s ↦ Ψ (s, 0)
  have hT : 0 < T := mul_pos (by norm_num) L.sourceRadius_pos
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hadm {s : InitialData (Euclidean (n - 1))} {t : ℝ}
      (hs : s ∈ ball a.baseData T) (ht : t ∈ Ioo (-T) T) :
      (t, s) ∈ (L.flow Q).time ×ˢ (L.flow Q).parameters := by
    apply L.source_admissible Q
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro ht hs
  have hND : closedBall (0, ξ) N.stateRadius ⊆ N.stateDomain := by
    simpa only [a.baseState_eq] using N.stateBall_subset
  have hDH : N.stateDomain ⊆ H.domain := fun z hz ↦
    ⟨hdomain z hz, (mem_frozenSymbol_domain z).mp (N.state_subset hz)⟩
  have hH : ContDiffOn ℝ ∞ H.h N.stateDomain :=
    (contDiffOn_normalizedSymbol hU Q.2.1).mono hDH
  have hV : ContDiffOn ℝ ∞ H.vectorField N.stateDomain :=
    H.contDiffOn_vectorField_of_subset N.state_open hDH (by simpa using hH)
  have hΨ : ContinuousOn Ψ (ball a.baseData T ×ˢ Ioo (-T) T) := by
    have hc : ContinuousOn (fun q ↦ ((L.flow Q).position q, (L.flow Q).momentum q))
        ((L.flow Q).time ×ˢ (L.flow Q).parameters) := by
      intro q hq
      exact (((L.flow Q).position_derivative _ hq.1 _ hq.2).continuousAt.prodMk
        ((L.flow Q).momentum_derivative _ hq.1 _ hq.2).continuousAt).continuousWithinAt
    exact hc.comp (continuous_snd.prodMk continuous_fst).continuousOn
      (fun q hq ↦ hadm hq.1 hq.2)
  have hrange (s) (hs : s ∈ ball a.baseData T) (t) (ht : t ∈ Ioo (-T) T) :
      Ψ (s, t) ∈ closedBall (0, ξ) N.stateRadius := L.state_mem Q _ (hadm hs ht)
  have hode (s) (hs : s ∈ ball a.baseData T) (t) (ht : t ∈ Ioo (-T) T) :
      HasDerivAt (fun τ ↦ Ψ (s, τ)) (H.vectorField (Ψ (s, t))) t :=
    ((L.flow Q).position_hasDerivAt (hadm hs ht).1 (hadm hs ht).2).prodMk
      ((L.flow Q).momentum_hasDerivAt (hadm hs ht).1 (hadm hs ht).2)
  let k : ℝ≥0 := ⟨cNorm (closedBall (0, ξ) N.stateRadius) 2 H.vectorField,
    cNorm_nonneg _ _ _⟩
  have hlipV := (field_and_fderiv_lipschitzOnWith_of_cNorm
    (K := k) N.state_open hND hV le_rfl).1
  have hsmooth {r : ℝ} (hr : r < T) :
      ContDiffOn ℝ ∞ Ψ (ball a.baseData r ×ˢ Ioo (-T) T) := by
    have hσ : ∀ s ∈ closedBall a.baseData r, ContDiffAt ℝ 2 σ s := fun s hs ↦
      ((retained_initialState_smooth L Q).contDiffAt
        (isOpen_ball.mem_nhds (closedBall_subset_ball hr hs))).of_le (by simp)
    let b : ℝ≥0 := ⟨cNorm (closedBall a.baseData r) 2 σ, cNorm_nonneg _ _ _⟩
    have hlipσ : LipschitzOnWith b σ (ball a.baseData r) := by
      apply (convex_ball _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun s hs ↦ (hσ s (ball_subset_closedBall hs)).differentiableAt (by norm_num))
      intro s hs
      exact (norm_and_fderiv_le_cNorm_two (isCompact_closedBall _ _) hσ
        (ball_subset_closedBall hs)).2
    let k' : ℝ≥0 := ⟨(b : ℝ) * Real.exp ((k : ℝ) * T), by positivity⟩
    apply contDiffOn_retained_section_flow N.state_open hV isOpen_ball hzero
      (hΨ.mono (prod_mono (ball_subset_ball hr.le) (Subset.refl _)))
      (fun s hs t ht ↦ hND (hrange s (ball_subset_ball hr.le hs) t ht))
      ((retained_initialState_smooth L Q).mono (ball_subset_ball hr.le)) (fun _ _ ↦ rfl)
      (fun s hs t ht ↦ hode s (ball_subset_ball hr.le hs) t ht)
      (K := k')
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs u hu
    have hsub : uIcc 0 t ⊆ Ioo (-T) T := ordConnected_Ioo.uIcc_subset hzero ht
    have hs' := ball_subset_ball hr.le hs
    have hu' := ball_subset_ball hr.le hu
    have hb := norm_le_gronwallBound_of_hasDerivAt_uIcc
      (R := fun τ ↦ Ψ (s, τ) - Ψ (u, τ))
      (R' := fun τ ↦ H.vectorField (Ψ (s, τ)) - H.vectorField (Ψ (u, τ)))
      (fun τ hτ ↦ (hode s hs' τ (hsub hτ)).sub (hode u hu' τ (hsub hτ)))
      (hlipσ.norm_sub_le hs hu) (L := k) (ε := 0) (fun τ hτ ↦ by
        simpa only [add_zero] using hlipV.norm_sub_le
          (hrange s hs' τ (hsub hτ)) (hrange u hu' τ (hsub hτ)))
    have ht' : |t - 0| ≤ T := by simpa using (abs_lt.mpr ht).le
    have hb' := hb.trans (gronwallBound_mono (mul_nonneg b.coe_nonneg (norm_nonneg _))
      le_rfl k.coe_nonneg ht')
    rw [gronwallBound_ε0] at hb'
    change dist (Ψ (s, t)) (Ψ (u, t)) ≤ ((b : ℝ) * Real.exp ((k : ℝ) * T)) * dist s u
    simp only [dist_eq_norm]
    nlinarith only [hb']
  intro q hq
  have hqs : q.1 ∈ Ioo (-T) T ∧ q.2 ∈ ball a.baseData T := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
      Real.norm_eq_abs, abs_lt, mem_Ioo] using hq
  obtain ⟨r, hqr, hr⟩ := exists_between (show dist q.2 a.baseData < T from hqs.2)
  have hloc : ContDiffAt ℝ ∞ Ψ (q.2, q.1) :=
    (hsmooth hr).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hqr, hqs.1⟩)
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ × InitialData (Euclidean (n - 1)) ↦
      Ψ (z.2, z.1)) q := hloc.comp q (contDiffAt_snd.prodMk contDiffAt_fst)
  exact hc.contDiffWithinAt

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
