module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhase
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SharpPhaseBounds

/-!
# Quantitative bounds for the actual adapted phase

The coordinate restriction of the SAME current Hamilton chart has arbitrary
finite-order comparison with the explicit frozen affine phase, and sharp
immersion order `m+3`. These discharge the phase input, as distinct from the
remaining chart/domain inputs, of `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualPhase
open HamiltonPhase ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Pullback of the current phase seminorm to its actual orthogonal,
zero-energy coordinates costs no derivatives
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem cNorm_current_le (Q : _) (m : ℕ)
    {K : Set (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1))}
    (hK : K ⊆ closedBall (0, covectorCenter T) T.family.radius) :
    cNorm K m (current T Q) ≤ (m + 1 : ℝ) *
      cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) T.family.radius) m
        (phase (T.currentChart Q).coordinates) := by
  exact InverseEstimates.cNorm_comp_contraction_le_on
    (adaptedPhaseInclusion T.data.adapted) (norm_adaptedPhaseInclusion_le _)
    (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith [T.family.radius_pos]))
    (T.family.phase_smooth Q) (fun _ h ↦ (inclusion_mem_closedBall T).mpr (hK h)) m

private theorem cNorm_reference_error_eq (Q : _) (m : ℕ)
    {K : Set (WithLp 2 (ℝ × Euclidean (n - 1)) × Euclidean (n - 1))}
    (hK : K ⊆ closedBall (0, covectorCenter T) T.family.radius) :
    cNorm K m (current T Q - Comparison.referencePhase (dispersion T)) =
      cNorm K m (current T Q - reference T) := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro q hq
  have he : current T Q - Comparison.referencePhase (dispersion T) =ᶠ[𝓝 q]
      current T Q - reference T := by
    filter_upwards [isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) (hK hq))] with w hw
    simp only [Pi.sub_apply, reference_eq_affine T hw]
  exact congrArg norm ((he.iteratedFDeriv ℝ j).eq_of_nhds)

/-- Every prescribed positive phase `C^m` error follows from primitive frame
`C^(m+1)` closeness, on the SAME fixed phase chart. In particular `m = 4`
discharges the phase-error premise of `exists_phaseCharts_c1_comparison`;
`m = 5` uses the paper's frame `C^6` neighborhood
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_current_comparison_threshold (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 1)
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ K ⊆ closedBall (0, covectorCenter T) T.family.radius,
        cNorm K m (current T Q - Comparison.referencePhase (dispersion T)) < ε := by
  have hm : 0 < (m + 1 : ℝ) := by positivity
  obtain ⟨δ, hδ, hc⟩ := T.current_phase_continuity m (div_pos hε hm)
  refine ⟨δ, hδ, fun Q hQ K hK ↦ ?_⟩
  rw [cNorm_reference_error_eq T Q m hK]
  have hs : ContDiffOn ℝ ∞ (phase T.reference.chart.coordinates)
      (ball (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) (2 * T.family.radius)) := by
    have hh : ContDiffOn ℝ ∞ T.data.localReference.family.chart.coordinates
        T.data.localReference.family.chart.target := by
      rw [T.data.localReference.family.reference_control.target_eq]
      exact T.data.localReference.family.reference_control.coordinates_smooth
    exact (T.data.localReference.family.chart.contDiffOn_phase hh).mono T.family.reference_target
  have hb := InverseEstimates.cNorm_comp_contraction_le_on
    (adaptedPhaseInclusion T.data.adapted) (norm_adaptedPhaseInclusion_le _)
    (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith [T.family.radius_pos]))
    ((T.family.phase_smooth Q).sub hs)
    (fun _ h ↦ (inclusion_mem_closedBall T).mpr (hK h)) m
  apply hb.trans_lt
  exact (mul_lt_mul_of_pos_left (hc Q hQ) hm).trans_eq (mul_div_cancel₀ _ hm.ne')

/-- The actual adapted phase retains the sharp immersion order `m+3`.
Consequently the inverse estimates' phase order `r+3` uses immersion order
`r+6`, with constants chosen before the immersion
(`app:ch_seed:prop:seed-phase-charts`, final paragraph). -/
theorem exists_current_projected_sharp_bound {N : ℕ}
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ C₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m K, K ⊆ closedBall (0, covectorCenter T) T.family.radius →
          cNorm K m (current T Q) ≤ A m * (1 + cNorm KF (m + 3) F) := by
  obtain ⟨A, hA, hb⟩ := T.exists_projected_phase_sharp_bound hKF hKU hball C₀ hκmet hκ
  refine ⟨fun m ↦ (m + 1 : ℝ) * A m, fun m ↦ mul_pos (by positivity) (hA m), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow Q m K hK
  exact (cNorm_current_le T Q m hK).trans
    ((mul_le_mul_of_nonneg_left (hb F hF hi hrank hlowF hmet hnormal hlow m)
      (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end JanetCartan.FullPhaseCharts.ActualPhase
