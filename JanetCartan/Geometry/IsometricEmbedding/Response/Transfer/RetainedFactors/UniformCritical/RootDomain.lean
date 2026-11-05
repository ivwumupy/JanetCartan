module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.RootMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualGaps

/-!
# A common primary domain for the retained root

The original `C⁶` coefficient comparison places the actual primary covectors
in the retained root's uniqueness neighborhood. Both the coefficient threshold
and the buffered parameter ball are chosen before the varying field. The whole
original physical ball is retained, as are the primary chart and the anchored
coefficient root.

Consumer: the uniform primary critical construction for
`app:ch_response:eq:response-exact-phase` and
`app:ch_response:eq:direct-envelope-profile`. This supplies its eikonal domain;
it does not yet construct the moving critical points.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ArbitraryAccuracy
open RegularSector.Characteristic RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.RootFamily ResponseTransfer.RetainedFactors

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

private theorem physical_mem_frameBall
    (Q : {Q : E → Coeff // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    {x : E} {c : Euclidean 3}
    (hx : x ∈ ball 0 T.physicalRadius) (hc : c ∈ parameterInterior (2 * P.radius)) :
    x ∈ closedBall 0 T.data.localReference.stateRadius := by
  have ht := T.reference.target_contains x hx c hc
  have ha := (T.currentChart Q).source_admissible _
    ((T.currentChart Q).maps_to_source _ ht)
  have hs := T.family.state_mem Q
    (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch c)))
    ⟨ha.1, ha.2⟩
  have hpos : (T.family.flow Q).position
      (chartLift (T.currentChart Q).coordinates (x, (0, T.reference.spatialPatch c))) = x :=
    (T.currentChart Q).right_inverse (x, (0, T.reference.spatialPatch c)) ht
  rw [hpos] at hs
  exact (show dist x 0 ≤ dist (x, _) (0, T.data.center) by
    rw [Prod.dist_eq]; exact le_max_left _ _).trans hs

/-- One coefficient threshold and one fourfold parameter buffer place the
ORIGINAL primary coefficient/covector pair in any prescribed open frozen
neighborhood. The entire original physical ball is covered, uniformly in
`Q`. The geometric frame-ball inclusion is supplied by
`frameBall_subset_of_stateDomain` in the original reference construction;
the analytic comparison is proved by
`NullTransport.exists_buffered_carrier_value_threshold`
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_uniform_primary_pair_neighborhood
    {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Euclidean 3} (hc₀ : c₀ ∈ parameterInterior (2 * P.radius))
    {V : Set (Coeff × E)} (hV : IsOpen V)
    (hbase : (cubeStress (d + 1), P.toFun c₀) ∈ V) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        ∀ x ∈ ball (0 : E) T.physicalRadius, ∀ c ∈ closedBall c₀ (4 * s),
          (Q.1 x, T.carrierGradient Q x c) ∈ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hbase)
  have hpc : ContinuousAt P.toFun c₀ :=
    (hP.2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds hc₀)).continuousAt
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_parameterInterior _).mem_nhds hc₀)
      (hpc.preimage_mem_nhds (ball_mem_nhds (P.toFun c₀) (half_pos hε))))
  obtain ⟨δ₀, hδ₀, hcomp⟩ :=
    NullTransport.exists_buffered_carrier_value_threshold T (half_pos hε)
  let δ := min T.family.threshold (min (ε / 2) δ₀)
  have hs : 0 < η / 8 := by positivity
  have hsub : closedBall c₀ (4 * (η / 8)) ⊆ ball c₀ η :=
    closedBall_subset_ball (by linarith)
  refine ⟨δ, lt_min T.family.threshold_pos (lt_min (half_pos hε) hδ₀),
    min_le_left _ _, η / 8, hs, fun c hc ↦ (hηsub (hsub hc)).1, ?_⟩
  intro Q hQ x hx c hc
  have hc' := hηsub (hsub hc)
  have hQdiff : ∀ y ∈ closedBall (0 : E) T.data.localReference.stateRadius,
      ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress (d + 1)) y := by
    intro y hy
    exact ((Q.2.1.contDiffAt (hU.mem_nhds (hframe hy))).sub contDiffAt_const).of_le
      (by simp)
  have hv := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
    hQdiff (T.physical_mem_frameBall Q hx hc'.1) (Nat.zero_le 6)
  have hvalue : dist (Q.1 x) (cubeStress (d + 1)) < ε := by
    have hlow : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < ε / 2 :=
      hQ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hh : ‖Q.1 x - cubeStress (d + 1)‖ ≤
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hv
    rw [dist_eq_norm]
    exact (hh.trans_lt hlow).trans (half_lt_self hε)
  have hgrad : dist (T.carrierGradient Q x c) (P.toFun c) < ε / 2 := by
    rw [dist_eq_norm]
    exact hcomp Q (hQ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
      x hx c hc'.1
  apply hεV
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨hvalue, (dist_triangle _ (P.toFun c) _).trans_lt ?_⟩
  have hp : dist (P.toFun c) (P.toFun c₀) < ε / 2 := hc'.2
  linarith

/-- A common buffered eikonal domain for the SAME retained coefficient root
and the ORIGINAL primary phase. The threshold and parameter radius precede
every varying field; neither is obtained from pointwise continuity in `Q`.
Smoothness is joint in position and primary parameters, and the equation
also holds on the closed fourfold parameter buffer. This closes the
root-matching input to the uniform critical construction, without selecting
the independent chart of `Compatible.PrimaryCritical`
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_uniform_retained_primary_root_domain
    {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (hframe : closedBall (0 : E) T.data.localReference.stateRadius ⊆ U)
    {c₀ : Euclidean 3} (hc₀ : c₀ ∈ parameterInterior (2 * P.radius))
    (hξ : P.toFun c₀ ≠ 0) {i r c' : Fin (d + 1)}
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c' (cubeStress (d + 1)) (P.toFun c₀) H ε L μ ν) :
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧ ∃ s > (0 : ℝ),
      closedBall c₀ (4 * s) ⊆ parameterInterior (2 * P.radius) ∧
      ∀ Q, cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (d + 1)) < δ →
        let X := (primaryCoordinateChange i).symm ⁻¹' ball (0 : E) T.physicalRadius
        let Ω := X ×ˢ ball c₀ (4 * s)
        IsOpen Ω ∧ Convex ℝ Ω ∧
        ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) Ω ∧
        ContDiffOn ℝ ∞ (fun q : E × Euclidean 3 ↦
          gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) Ω ∧
        ∀ q ∈ X ×ˢ closedBall c₀ (4 * s),
          rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
            (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) = 0 := by
  obtain ⟨V, hV, hbase, hprimary⟩ :=
    T.exists_retained_primary_root_domain hP hξ hε hL hμ hν hH
  obtain ⟨δ, hδ, hδT, s, hs, hparam, hpair⟩ :=
    T.exists_uniform_primary_pair_neighborhood hP hframe hc₀ hV hbase
  refine ⟨δ, hδ, hδT, s, hs, hparam, ?_⟩
  intro Q hQ X Ω
  obtain ⟨_, hφ, he⟩ := hprimary Q
  have hmem (q : E × Euclidean 3) (hq : q ∈ X ×ˢ closedBall c₀ (4 * s)) :
      (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
        q.2 ∈ parameterInterior (2 * P.radius) ∧
        (Q.1 ((primaryCoordinateChange i).symm q.1),
          T.carrierGradient Q ((primaryCoordinateChange i).symm q.1) q.2) ∈ V :=
    ⟨hq.1, hparam hq.2, hpair Q hQ _ hq.1 _ hq.2⟩
  have hΩ : IsOpen Ω :=
    (isOpen_ball.preimage (primaryCoordinateChange i).symm.continuous).prod isOpen_ball
  have hsm : ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) Ω :=
    hφ.mono (fun q hq ↦ hmem q ⟨hq.1, ball_subset_closedBall hq.2⟩)
  refine ⟨hΩ,
    ((convex_ball (0 : E) T.physicalRadius).linear_preimage
      (primaryCoordinateChange i).symm.toLinearMap).prod (convex_ball c₀ (4 * s)),
    hsm, ?_, fun q hq ↦ he q (hmem q hq)⟩
  let F : E × Euclidean 3 → E × Euclidean 3 :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2)
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  apply ((primaryCoordinateChange i).contDiff.comp_contDiffOn
    ((T.carrierGradient_smooth hP Q).comp hF.contDiffOn
      (fun q hq ↦ ⟨hq.1, hparam (ball_subset_closedBall hq.2)⟩))).congr
  intro q hq
  exact T.primaryPhaseInCoordinates_gradient hP i Q hq.1
    (hparam (ball_subset_closedBall hq.2))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
