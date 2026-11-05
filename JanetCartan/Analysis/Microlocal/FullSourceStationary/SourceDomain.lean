module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.FullSourceIncidence

/-!
# A uniform root domain for the original full source

The free covector and the three source labels remain independent. The original
full momentum comparison and compact incidence protection give one parameter
cap and coefficient threshold before the varying field. This is the root-domain
input of the full-source stationary constructor for
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart ResponseTransfer.RetainedFactors
open LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- The whole closed physical buffer and every original free covector in
the phase ball lie in the same full source domain. No carrier restriction is
used (`app:ch_response:eq:response-exact-phase`). -/
theorem full_source_mem_phaseDomain_of_physical_buffer
    {x : E} (hx : x ∈ closedBall 0 T.physicalRadius) {c : Param}
    (hc : c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius) :
    (x, c.2) ∈ phaseDomain T := by
  have hr : T.physicalRadius < T.family.radius := by
    have hp := T.physicalRadius_pos
    have hm := min_le_left T.family.radius (3 * T.family.sourceRadius)
    dsimp only [physicalRadius] at hp ⊢
    linarith
  exact max_lt ((mem_closedBall.mp hx).trans_lt hr) hc

/-- The original coefficient/covector incidence neighborhood is uniform on
the entire physical buffer, with a fourfold ball in the FULL source parameters.
The actual full momentum comparison supplies the coefficient threshold; the
frozen covector's continuity supplies the parameter cap. Both choices precede
the varying field (`app:ch_response:eq:response-exact-phase`). -/
theorem exists_uniform_full_source_parameter_neighborhood
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Param}
    (hc₀ : c₀.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {V : Set (Coeff × E)} (hV : IsOpen V)
    (hbase : (cubeStress (d + 1), T.reference.covector (0, c₀.2)) ∈ V) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆
        univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ x ∈ closedBall (0 : E) T.physicalRadius, ∀ c ∈ closedBall c₀ (4 * s),
          (Q.1 x, phaseGradient T Q x c.2) ∈ V := by
  let A : Set Param :=
    univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius
  have hA : IsOpen A := isOpen_univ.prod isOpen_ball
  have hcA : c₀ ∈ A := ⟨mem_univ _, hc₀⟩
  have hzero (c : Param) (hc : c ∈ A) : ((0 : E), c) ∈ domain T :=
    T.full_source_mem_phaseDomain_of_physical_buffer
      (mem_closedBall_self T.physicalRadius_pos.le) hc.2
  have hcont : ContinuousOn
      (fun c : Param ↦ (cubeStress (d + 1), T.reference.covector (0, c.2))) A :=
    T.continuousOn_frozen_full_source_pair.comp
      (continuousOn_const.prodMk continuousOn_id) hzero
  have hnear := (hcont.continuousAt (hA.mem_nhds hcA)).preimage_mem_nhds
    (hV.mem_nhds hbase)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hA.mem_nhds hcA) hnear)
  let s := η / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hsub : closedBall c₀ (4 * s) ⊆ ball c₀ η :=
    closedBall_subset_ball (by dsimp [s]; linarith)
  have hparam : closedBall c₀ (4 * s) ⊆ A := fun c hc ↦ (hηsub (hsub hc)).1
  let J : Set (E × Param) := closedBall (0 : E) T.physicalRadius ×ˢ closedBall c₀ (4 * s)
  have hJ : IsCompact J := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hJO : J ⊆ domain T := fun w hw ↦
    T.full_source_mem_phaseDomain_of_physical_buffer hw.1 (hparam hw.2).2
  obtain ⟨δ, hδ, hδT, hpair⟩ := T.exists_uniform_full_source_pair_neighborhood
    hframe hJ hJO hV (fun w hw ↦ (hηsub (hsub hw.2)).2)
  exact ⟨δ, hδ, hδT, s, hs, hparam,
    fun Q hQ x hx c hc ↦ hpair Q hQ (x, c) ⟨hx, hc⟩⟩

/-- A fixed full-source eikonal domain for the SAME retained root, anchored
at the original reference covector. Joint smoothness, smooth gradient, and the
root equation follow from the actual full source; the fourfold parameter cap
and coefficient threshold precede all histories and operators. This supplies
the source-domain input of `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_uniform_retained_full_source_root_domain
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Param}
    (hc₀ : c₀.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hξ : T.reference.covector (0, c₀.2) ≠ 0) {i row col : Fin (d + 1)}
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i row col (cubeStress (d + 1))
      (T.reference.covector (0, c₀.2)) H ε L μ ν) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆
        univ ×ˢ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
        let Ω := X ×ˢ ball c₀ (4 * s)
        IsOpen Ω ∧ Convex ℝ Ω ∧
        ContDiffOn ℝ ∞ (fun q ↦ T.fullSourcePhaseInCoordinates i Q q.1 q.2) Ω ∧
        ContDiffOn ℝ ∞ (fun q : E × Param ↦
          gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) Ω ∧
        ∀ q ∈ X ×ˢ closedBall c₀ (4 * s),
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
            (q.1, gradient (fun y ↦ T.fullSourcePhaseInCoordinates i Q y q.2) q.1) = 0 := by
  obtain ⟨V, hV, hbase, hroot⟩ := T.exists_retained_full_source_root_domain
    hξ hε hL hμ hν hH
  obtain ⟨δ, hδ, hδT, s, hs, hparam, hpair⟩ :=
    T.exists_uniform_full_source_parameter_neighborhood hframe hc₀ hV hbase
  refine ⟨δ, hδ, hδT, s, hs, hparam, ?_⟩
  intro Q hQ X Ω
  have hmem (q : E × Param) (hq : q ∈ X ×ˢ closedBall c₀ (4 * s)) :
      ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T ∧
        (Q.1 ((primaryCoordinateChange i).symm q.1),
          phaseGradient T Q ((primaryCoordinateChange i).symm q.1) q.2.2) ∈ V :=
    ⟨T.full_source_mem_phaseDomain_of_physical_buffer
      (ball_subset_closedBall hq.1) (hparam hq.2).2,
      hpair Q hQ _ (ball_subset_closedBall hq.1) _ hq.2⟩
  have hΩ : IsOpen Ω :=
    (isOpen_ball.preimage (primaryCoordinateChange i).symm.continuous).prod isOpen_ball
  refine ⟨hΩ, ((convex_ball (0 : E) T.physicalRadius).linear_preimage
    (primaryCoordinateChange i).symm.toLinearMap).prod (convex_ball _ _),
    (hroot Q).2.1.mono (fun q hq ↦ hmem q ⟨hq.1, ball_subset_closedBall hq.2⟩),
    ?_, fun q hq ↦ (hroot Q).2.2 q (hmem q hq)⟩
  let F : E × Param → E × Euclidean d :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2.2)
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd.snd
  apply ((primaryCoordinateChange i).contDiff.comp_contDiffOn
    ((phaseGradient_smooth T Q).comp hF.contDiffOn
      (fun q hq ↦ (hmem q ⟨hq.1, ball_subset_closedBall hq.2⟩).1))).congr
  intro q hq
  exact T.fullSourcePhaseInCoordinates_gradient i Q
    (hmem q ⟨hq.1, ball_subset_closedBall hq.2⟩).1

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
