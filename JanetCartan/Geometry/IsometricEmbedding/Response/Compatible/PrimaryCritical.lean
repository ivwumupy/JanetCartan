module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.LocalEvolution
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.AveragedHessian

/-!
# Constructed critical points for the same selected primary phase

Instantiate the stationary inverse construction for `T.currentChart Q`, then
apply its already proved two-time compatibility. This closes local existence,
uniqueness and smooth dependence of the actual critical point, with zero
critical value, in `paper-v2.tex`, `app:ch_response:lem:energy-carrier-jets`.
It also constructs a common bound for every segment-averaged Hessian on a
smaller local convex box. It does not assert coefficient-uniform choices on
the whole signed patch or the fixed response operator theorem.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.CompatibleResponse

/-- Joint primary-gradient smoothness follows from joint phase smoothness.
This is the derivative input to `exists_elapsedStationary_branch`, retaining
all primary parameters (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_joint_primaryGradient {n : ℕ}
    {φ : Euclidean n → Euclidean 3 → ℝ} {Ω : Set (Euclidean n × Euclidean 3)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) Ω := by
  intro q hq
  have hf : ContDiffAt ℝ ∞
      (fun v : (Euclidean n × Euclidean 3) × Euclidean n ↦ φ v.2 v.1.2) (q, q.1) :=
    (hφ.contDiffAt (hΩ.mem_nhds hq)).comp (q, q.1)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hd : ContDiffAt ℝ ∞
      (fun p : Euclidean n × Euclidean 3 ↦ fderiv ℝ (fun z ↦ φ z p.2) p.1) q :=
    hf.fderiv contDiffAt_fst (by simp)
  exact ((InnerProductSpace.toDual ℝ (Euclidean n)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    q hd).contDiffWithinAt

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open FrozenMenu CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open ResponseTransfer.DirectEvolution
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual primary chart admits a smooth, unique local critical point for
its direct elapsed modulated phase, with exactly zero critical value. Both
orientations of elapsed time occur in the same open neighborhood of zero;
all nearby output positions and original primary parameters use one chart.
The flow/root and compatibility are obtained from
`exists_primary_local_twoTime_compatibility`, not assumed.

This closes the local stationary-point obligation of
`app:ch_response:lem:energy-carrier-jets`. The full compact signed-patch,
coefficient-uniform choices and the fixed response still remain. -/
theorem exists_primary_local_twoTime_critical_branch {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (Q : _) {x₀ : Euclidean (d + 1)} {c₀ : Euclidean 3}
    (hx₀ : x₀ ∈ ball 0 T.physicalRadius) (hc₀ : c₀ ∈ parameterInterior (2 * P.radius)) :
    ∃ i : Fin (d + 1),
    ∃ C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
    ∃ V : Set (ℝ × (Euclidean (d + 1) × Euclidean 3)),
    ∃ B : Set (Euclidean (d + 1) × Euclidean (d + 1)),
    ∃ κ : (ℝ × (Euclidean (d + 1) × Euclidean 3)) →
      Euclidean (d + 1) × Euclidean (d + 1),
      let x := primaryCoordinateChange i x₀
      let φ := T.primaryPhaseInCoordinates i Q
      IsOpen V ∧ (0, (x, c₀)) ∈ V ∧ IsOpen B ∧
      (x, gradient (fun z ↦ φ z c₀) x) ∈ B ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧ ContDiffOn ℝ ∞ κ V ∧
      κ (0, (x, c₀)) = (x, gradient (fun z ↦ φ z c₀) x) ∧ MapsTo κ V B ∧
      (∀ q ∈ V, ∀ w ∈ B,
        (primaryCoordinateChange i).symm q.2.1 ∈ ball 0 T.physicalRadius ∧
        (primaryCoordinateChange i).symm w.1 ∈ ball 0 T.physicalRadius ∧
        q.2.2 ∈ parameterInterior (2 * P.radius) ∧
        elapsedChartPoint q.1 q.2.1 w.2 ∈ C.target ∧
        (fderiv ℝ (elapsedStationarySystem C φ) (q, w) ∘L
          .inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
            (Euclidean (d + 1) × Euclidean (d + 1))).IsInvertible ∧
        IsUnit (fderiv ℝ (gradient (elapsedCarrierPhase (chartPhase C) q.1 φ q.2))
          (WithLp.toLp 2 w)) ∧
        (fderiv ℝ (elapsedModulatedPhase C q.1 (fun z ↦ φ z q.2.2) q.2.1) w = 0 ↔
          κ q = w)) ∧
      (∀ q ∈ V,
        FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) q.1)
          (κ q).1 (κ q).2 q.2.1 (gradient (fun z ↦ φ z q.2.2) q.2.1) ∧
        elapsedModulatedPhase C q.1 (fun z ↦ φ z q.2.2) q.2.1 (κ q) = 0 ∧
        gradient (elapsedCarrierPhase (chartPhase C) q.1 φ q.2) (WithLp.toLp 2 (κ q)) = 0 ∧
        elapsedCarrierPhase (chartPhase C) q.1 φ q.2 (WithLp.toLp 2 (κ q)) = 0) ∧
      ∃ δ > (0 : ℝ), ∃ s > (0 : ℝ), ∃ M > (0 : ℝ),
        ball (0, (x, c₀)) δ ⊆ V ∧
        (∀ w ∈ ball (WithLp.toLp 2 (x, gradient (fun z ↦ φ z c₀) x)) s, w.ofLp ∈ B) ∧
        MapsTo (fun q ↦ WithLp.toLp 2 (κ q)) (ball (0, (x, c₀)) δ)
          (ball (WithLp.toLp 2 (x, gradient (fun z ↦ φ z c₀) x)) s) ∧
        ∀ q ∈ ball (0, (x, c₀)) δ,
        ∀ w ∈ ball (WithLp.toLp 2 (x, gradient (fun z ↦ φ z c₀) x)) s,
          let H := averagedPhaseHessian
            (fun q ↦ elapsedCarrierPhase (chartPhase C) q.1 φ q.2)
            (fun q ↦ WithLp.toLp 2 (κ q)) q w
          IsUnit H ∧ ‖Ring.inverse H‖ ≤ M := by
  obtain ⟨i, D, h, ρ, hρ, s, _, R, _, ε, _, Φ, C,
    _, _, _, _, hcontain, hφ, _, hC, hsource, htarget, hsmooth,
    _, hinverse, hphase, hi, _, hcrit⟩ :=
    T.exists_primary_local_twoTime_compatibility hP Q hx₀ hc₀
  let x := primaryCoordinateChange i x₀
  let φ := T.primaryPhaseInCoordinates i Q
  let p := gradient (fun z ↦ φ z c₀) x
  let Ω := ball x (2 * ρ) ×ˢ ball c₀ ρ
  have hΩ : IsOpen Ω := isOpen_ball.prod isOpen_ball
  have hΩsub : Ω ⊆ closedBall x (4 * ρ) ×ˢ closedBall c₀ (4 * ρ) := by
    intro q hq
    exact ⟨closedBall_subset_closedBall (by linarith : 2 * ρ ≤ 4 * ρ) (ball_subset_closedBall hq.1),
      closedBall_subset_closedBall (by linarith : ρ ≤ 4 * ρ) (ball_subset_closedBall hq.2)⟩
  have hφΩ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω := hφ.mono hΩsub
  have hg := contDiffOn_joint_primaryGradient hΩ hφΩ
  have hxc : (x, c₀) ∈ Ω := ⟨mem_ball_self (by positivity), mem_ball_self hρ⟩
  have hq : elapsedChartPoint 0 x p ∈ C.target := by
    simpa only [elapsedChartPoint, spacetimeRootState, sub_zero] using htarget
  obtain ⟨V, B, κ, hV, hv, hB, hb, hk, hk₀, hmaps, hdata⟩ :=
    exists_elapsedStationary_branch hC hsource hi hinverse hΩ hg hxc hq
  have hstat q (hqV : q ∈ V) w (hw : w ∈ B) :
      fderiv ℝ (elapsedModulatedPhase C q.1 (fun z ↦ φ z q.2.2) q.2.1) w = 0 ↔ κ q = w := by
    have hd := hdata q hqV w hw
    have hdiff : DifferentiableAt ℝ (fun z ↦ φ z q.2.2) w.1 :=
      ((hφΩ.contDiffAt (hΩ.mem_nhds hd.1)).comp w.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    rw [elapsedModulatedPhase_stationary_iff (hphase _ hd.2.1) hdiff]
    rw [← hd.2.2.2]
    simp only [elapsedStationarySystem, Prod.mk_eq_zero, sub_eq_zero]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩
  let Vfull := V ∩ Prod.snd ⁻¹' Ω
  have hVfull : IsOpen Vfull := hV.inter (hΩ.preimage continuous_snd)
  have hvfull : (0, (x, c₀)) ∈ Vfull := ⟨hv, hxc⟩
  refine ⟨i, C, Vfull, B, κ, hVfull, hvfull, hB, hb, hsmooth,
    hk.mono inter_subset_left, hk₀, (fun q hq ↦ hmaps hq.1), ?_, ?_, ?_⟩
  · intro q hqV w hw
    have hd := hdata q hqV.1 w hw
    have hc := hcontain _ (hΩsub hd.1)
    exact ⟨(hcontain q.2 (hΩsub hqV.2)).1, hc.1, hc.2, hd.2.1, hd.2.2.1,
      isUnit_fderiv_gradient_elapsedCarrierPhase hphase hinverse hΩ hφΩ hg
        (w := WithLp.toLp 2 w) hd.1 hd.2.1 hd.2.2.1, hstat q hqV.1 w hw⟩
  · intro q hqV
    have hd := hdata q hqV.1 (κ q) (hmaps hqV.1)
    have hc := hcrit q.2.2 hd.1.2 q.1 q.2.1 (κ q).1 (κ q).2 hd.1.1 hd.2.1
      ((hstat q hqV.1 (κ q) (hmaps hqV.1)).mpr rfl)
    refine ⟨hc.1, hc.2, ?_, hc.2⟩
    rw [gradient_elapsedCarrierPhase (φ := φ) (c := q.2.2) (x := q.2.1) (hphase _ hd.2.1)
      (((hφΩ.contDiffAt (hΩ.mem_nhds hd.1)).comp (κ q).1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))]
    rw [hd.2.2.2.mpr rfl]
    rfl

  · let q₀ : ℝ × (Euclidean (d + 1) × Euclidean 3) := (0, (x, c₀))
    let w₀ : CarrierVariables (d + 1) := WithLp.toLp 2 (x, p)
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
    let f := fun q : ℝ × (Euclidean (d + 1) × Euclidean 3) ↦
      elapsedCarrierPhase (chartPhase C) q.1 φ q.2
    have hf : ContDiffAt ℝ ∞ (Function.uncurry f) (q₀, w₀) :=
      contDiffAt_joint_elapsedCarrierPhase (hsmooth.contDiffAt (C.open_target.mem_nhds hq))
        (hφΩ.contDiffAt (hΩ.mem_nhds hxc)) (hφΩ.contDiffAt (hΩ.mem_nhds hxc))
    have hunit : IsUnit (fderiv ℝ (gradient (f q₀)) w₀) :=
      isUnit_fderiv_gradient_elapsedCarrierPhase hphase hinverse hΩ hφΩ hg hxc hq
        (hdata q₀ hv (x, p) hb).2.2.1
    obtain ⟨η, hη, M, hM, hgap⟩ := exists_local_averaged_carrierHessian_gap hf hunit
    have hBmem : e ⁻¹' B ∈ 𝓝 w₀ := e.continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hb)
    obtain ⟨s, hs, hsball⟩ := Metric.mem_nhds_iff.mp
      (Filter.Eventually.and (ball_mem_nhds w₀ hη) hBmem)
    have hkcont : ContinuousAt (fun q ↦ e.symm (κ q)) q₀ :=
      e.symm.continuous.continuousAt.comp (hk.contDiffAt (hV.mem_nhds hv)).continuousAt
    have hkbase : e.symm (κ q₀) = w₀ := by rw [hk₀]; rfl
    have hkmem : (fun q ↦ e.symm (κ q)) ⁻¹' ball w₀ s ∈ 𝓝 q₀ := by
      apply hkcont.preimage_mem_nhds
      rw [hkbase]
      exact ball_mem_nhds w₀ hs
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp
      (Filter.Eventually.and (ball_mem_nhds q₀ hη)
        (Filter.Eventually.and (hVfull.mem_nhds hvfull) hkmem))
    refine ⟨δ, hδ, s, hs, M, hM, (fun q hq ↦ (hd hq).2.1),
      (fun w hw ↦ (hsball hw).2), (fun q hq ↦ (hd hq).2.2), ?_⟩
    intro q hqδ w hw
    exact hgap q (hd hqδ).1 (e.symm (κ q)) (hsball (hd hqδ).2.2).1 w (hsball hw).1

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
