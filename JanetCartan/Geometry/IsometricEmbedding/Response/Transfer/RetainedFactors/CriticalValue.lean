module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.CriticalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.RootMatching
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.RetainedEvolution

/-!
# Zero critical value for the retained evolution

Shrink the domain of the original retained flow, without choosing another flow
or inverse chart. Continuity gives whole-segment containment in the primary
root buffers. The existing root conservation theorem then proves zero critical
value for this same chart. These are local statements; uniform history and
full supported-carrier containment remain separate obligations.

Consumer: the retained-factor application of
`app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:eq:response-exact-phase`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ResponseTransfer.RetainedFactors
open CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ConicPhase DirectEvolution

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "Par" => ℝ × (E × Euclidean 3)

/-- The original retained smooth flow stays in any prescribed open lift
buffer for nearby initial states and sufficiently small times of EITHER sign.
The ODE and initial values are retained from that flow, not reconstructed.
This supplies whole-segment containment for the primary conservation theorem
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_flow_lift_buffer
    {h : Z → ℝ} {D : Set Z} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    {Φ : Z × ℝ → Z} {z₀ w₀ : Z} {R r time : ℝ} (htime : 0 < time)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z₀ R r time Φ)
    (hw₀ : w₀ ∈ ball z₀ r) (hwD : w₀ ∈ D)
    {W B : Set E} (hW : IsOpen W) (hB : IsOpen B)
    (hbase : rootSuspensionState h 0 w₀ ∈ W ×ˢ B) :
    ∃ δ > (0 : ℝ),
      ∀ w ∈ ball w₀ δ, Φ (w, 0) = w ∧
        ∀ u ∈ Ioo (-δ) δ,
          HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u ∧
          rootSuspensionState h 0 (Φ (w, u)) ∈ W ×ˢ B := by
  have hlift : ContinuousAt (rootSuspensionState h 0) w₀ := by
    have hx : Continuous (fun z : Z ↦ timeSpacePoint z.1 z.2.1) :=
      timeSpacePointCLM.continuous.comp (continuous_fst.prodMk continuous_snd.fst)
    have hp₀ : ContinuousAt (fun z : Z ↦ (0 + h z, z.2.2)) w₀ :=
      (continuousAt_const.add (hh.contDiffAt (hD.mem_nhds hwD)).continuousAt).prodMk
        continuousAt_snd.snd
    have hp : ContinuousAt (fun z : Z ↦ timeSpacePoint (0 + h z) z.2.2) w₀ :=
      timeSpacePointCLM.continuous.continuousAt.comp hp₀
    exact hx.continuousAt.prodMk hp
  have hinit := hΦ.initial w₀ (ball_subset_closedBall hw₀)
  have hdom : (w₀, (0 : ℝ)) ∈ ball z₀ r ×ˢ Ioo (-time) time :=
    ⟨hw₀, by constructor <;> linarith⟩
  have hcont := hΦ.smooth.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hdom)
  have hcomp : ContinuousAt (fun p : Z × ℝ ↦ rootSuspensionState h 0 (Φ p)) (w₀, 0) := by
    exact (show ContinuousAt (rootSuspensionState h 0) (Φ (w₀, 0)) by
      simpa only [hinit] using hlift).comp hcont.continuousAt
  have hn := hcomp.preimage_mem_nhds ((hW.prod hB).mem_nhds (by simpa [hinit] using hbase))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_ball.prod isOpen_Ioo).mem_nhds hdom) hn)
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hw' : w ∈ ball z₀ r := (hδsub (show (w, (0 : ℝ)) ∈ ball (w₀, 0) δ by
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_lt_iff] using And.intro hw hδ)).1.1
  refine ⟨hΦ.initial w (ball_subset_closedBall hw'), ?_⟩
  intro u hu
  have hp : (w, u) ∈ ball (w₀, (0 : ℝ)) δ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨hw, hu⟩
  exact ⟨hΦ.hasDerivAt (ball_subset_closedBall hw') (hδsub hp).1.2, (hδsub hp).2⟩

/-- Near the primary diagonal, every stationary point of the SAME retained
two-time chart has zero critical value and the original outgoing primary
gradient. The whole-segment primary buffers are derived from continuity of
the retained flow and joint primary smoothness. The eikonal input is precisely
the local equation proved by `exists_retained_primary_root_domain`.

No new flow, chart, critical-value identity or envelope bound is assumed.
The neighborhood is local to the supplied coefficients and primary base point
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_local_critical_value_eventually
    {h : Z → ℝ} {D : Set Z} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (z.1, (z.2.1, a • z.2.2)) = a * h z)
    {φ : E → Euclidean 3 → ℝ} {Ω : Set (E × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω)
    (he : ∀ q ∈ Ω, rootSuspension h (q.1, gradient (fun y ↦ φ y q.2) q.1) = 0)
    {x₀ : E} {c₀ : Euclidean 3} (hxc : (x₀, c₀) ∈ Ω)
    {Φ : Z × ℝ → Z} {z₀ : Z} {R r time : ℝ} (htime : 0 < time)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z₀ R r time Φ)
    (hw₀ : spacetimeRootState (x₀, gradient (fun y ↦ φ y c₀) x₀) ∈ ball z₀ r)
    (hwD : spacetimeRootState (x₀, gradient (fun y ↦ φ y c₀) x₀) ∈ D)
    {C : OpenPartialHomeomorph T T}
    (hC : (C : T → T) = twoTimeProjection Φ)
    (hphase : ∀ q ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C q) q)
    (hclock : ∀ q ∈ C.target, (twoTimeState Φ (C.symm q)).1 = q.1) :
    ∀ᶠ v : Par × (E × E) in 𝓝 ((0, (x₀, c₀)), (x₀, gradient (fun y ↦ φ y c₀) x₀)),
      elapsedChartPoint v.1.1 v.1.2.1 v.2.2 ∈ C.target →
      fderiv ℝ (elapsedModulatedPhase C v.1.1 (fun y ↦ φ y v.1.2.2) v.1.2.1) v.2 = 0 →
      FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) v.1.1)
        v.2.1 v.2.2 v.1.2.1 (gradient (fun y ↦ φ y v.1.2.2) v.1.2.1) ∧
      elapsedModulatedPhase C v.1.1 (fun y ↦ φ y v.1.2.2) v.1.2.1 v.2 = 0 := by
  let g := fun q : E × Euclidean 3 ↦ gradient (fun y ↦ φ y q.2) q.1
  let p₀ := g (x₀, c₀)
  let w₀ := spacetimeRootState (x₀, p₀)
  obtain ⟨ρ, hρ, s, hs, hsub, hg, hprod⟩ :=
    exists_root_graph_buffers hΩ (contDiffOn_joint_primaryGradient hΩ hφ).continuousOn hxc hD hwD
  have hlift : rootSuspensionState h 0 w₀ = (x₀, p₀) := by
    have hh₀ : h w₀ = p₀ 0 := (sub_eq_zero.mp (he (x₀, c₀) hxc)).symm
    apply Prod.ext
    · exact timeSpacePoint_coordinates x₀
    · change timeSpacePoint (0 + h w₀) (spatialPart p₀) = p₀
      rw [zero_add, hh₀]
      exact timeSpacePoint_coordinates p₀
  obtain ⟨δ, hδ, hflow⟩ := exists_retained_flow_lift_buffer hD hh htime hΦ hw₀ hwD
    (W := ball x₀ (2 * ρ)) (B := ball p₀ s) isOpen_ball isOpen_ball
    (by rw [hlift]; exact ⟨mem_ball_self (by positivity), mem_ball_self hs⟩)
  have hstate : Continuous (fun v : Par × (E × E) ↦ spacetimeRootState v.2) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).continuous.comp
      continuous_snd.fst).prodMk
        ((spatialPartCLM.continuous.comp continuous_snd.fst).prodMk
          (spatialPartCLM.continuous.comp continuous_snd.snd))
  have htimeN : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds (by
    constructor <;> linarith)
  filter_upwards [
    hstate.continuousAt.preimage_mem_nhds (ball_mem_nhds w₀ hδ),
    (continuous_fst.fst.continuousAt : ContinuousAt (fun v : Par × (E × E) ↦ v.1.1) _).preimage_mem_nhds htimeN,
    (continuous_fst.snd.snd.continuousAt : ContinuousAt (fun v : Par × (E × E) ↦ v.1.2.2) _).preimage_mem_nhds
      (ball_mem_nhds c₀ hρ),
    (continuous_snd.fst.continuousAt : ContinuousAt (fun v : Par × (E × E) ↦ v.2.1) _).preimage_mem_nhds
      (ball_mem_nhds x₀ (by positivity : 0 < 2 * ρ))]
    with v hv hr hc hz
  intro hq hstat
  have hmem {y : E} (hy : y ∈ ball x₀ (4 * ρ)) : (y, v.1.2.2) ∈ Ω :=
    hsub ⟨ball_subset_closedBall hy,
      closedBall_subset_closedBall (by linarith : ρ ≤ 4 * ρ) (ball_subset_closedBall hc)⟩
  have hφ' : ContDiffOn ℝ ∞ (fun y ↦ φ y v.1.2.2) (ball x₀ (4 * ρ)) :=
    hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ hmem hy)
  have hWY : ball x₀ (2 * ρ) ⊆ closedBall x₀ (3 * ρ) :=
    fun _ hy ↦ closedBall_subset_closedBall (by linarith : 2 * ρ ≤ 3 * ρ) (ball_subset_closedBall hy)
  have hYΩ : closedBall x₀ (3 * ρ) ⊆ ball x₀ (4 * ρ) := closedBall_subset_ball (by linarith)
  have hgP : MapsTo (gradient (fun y ↦ φ y v.1.2.2)) (ball x₀ (2 * ρ)) (closedBall p₀ s) := by
    intro y hy
    have hb := hg (x := (y, v.1.2.2)) ⟨ball_subset_closedBall (hYΩ (hWY hy)),
      closedBall_subset_closedBall (by linarith : ρ ≤ 4 * ρ) (ball_subset_closedBall hc)⟩
    exact closedBall_subset_closedBall (by linarith : s / 2 ≤ s) (ball_subset_closedBall hb)
  have hseg : uIcc 0 v.1.1 ⊆ Ioo (-δ) δ := by
    intro u hu
    rcases le_total 0 v.1.1 with hpos | hneg
    · rw [uIcc_of_le hpos] at hu
      exact ⟨lt_of_lt_of_le (by linarith) hu.1, lt_of_le_of_lt hu.2 hr.2⟩
    · rw [uIcc_of_ge hneg] at hu
      exact ⟨lt_of_lt_of_le hr.1 hu.1, lt_of_le_of_lt hu.2 hδ⟩
  exact elapsedModulatedPhase_critical_value hD hh hhom isOpen_ball hφ' isOpen_ball
    (isCompact_closedBall x₀ (3 * ρ)) (isCompact_closedBall p₀ s) hWY hYΩ
    (fun q hq ↦ hprod ⟨closedBall_subset_closedBall (by linarith : 3 * ρ ≤ 4 * ρ) hq.1, hq.2⟩)
    hgP (fun y hy ↦ he _ (hmem (hYΩ (hWY hy)))) hC hz hq (hclock _ hq)
    (hphase _ hq) (hflow _ hv).1
    (fun u hu ↦ ((hflow _ hv).2 u (hseg hu)).1)
    (fun u hu ↦ ((hflow _ hv).2 u (hseg hu)).2.1)
    (fun u hu ↦ ball_subset_closedBall ((hflow _ hv).2 u (hseg hu)).2.2) hstat

end JanetCartan.ResponseTransfer.RetainedFactors
