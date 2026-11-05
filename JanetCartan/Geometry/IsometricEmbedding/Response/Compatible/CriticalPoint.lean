module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.TwoTimeCritical
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# A critical point of the literal elapsed phase

The stationary system in `paper-v2.tex`,
`app:ch_response:lem:energy-carrier-jets`, has an explicitly invertible
source/covector derivative at elapsed time zero. The implicit function theorem
constructs the critical point, jointly in elapsed time, output position and
primary parameters. Its inputs are the actual inverse chart and initial-value
identity of the two-time flow, not a critical-point or nondegeneracy assumption.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The initial base of the actual elapsed graph is the output base at elapsed
time zero. The chart inverse and the flow's initial condition prove the identity
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem elapsedInputBase_zero
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {w₀ : RootState (Euclidean d)} {R ε : ℝ}
    (hsource : C.source ⊆ twoTimeDomain w₀ R ε)
    (hi : ∀ w ∈ ball w₀ R, Φ (w, 0) = w)
    {x θ : Euclidean (d + 1)} (hq : elapsedChartPoint 0 x θ ∈ C.target) :
    elapsedInputBase C 0 x θ = x := by
  obtain ⟨ht, hs, _, hy⟩ := twoTimeChart_inverse_coordinates hC hq
  have hstate : twoTimeState Φ (C.symm (elapsedChartPoint 0 x θ)) =
      (C.symm (elapsedChartPoint 0 x θ)).2 := by
    change Φ (_, (C.symm (elapsedChartPoint 0 x θ)).1 -
      (C.symm (elapsedChartPoint 0 x θ)).2.1) = _
    rw [ht, hs]
    simpa only [elapsedChartPoint, sub_zero, sub_self] using
      hi _ (hsource (C.map_target hq)).1
  rw [hstate] at hy
  dsimp only [elapsedInputBase]
  rw [hy]
  simpa only [elapsedChartPoint, sub_zero] using timeSpacePoint_coordinates x

/-- The literal two stationary equations of the elapsed modulated phase.
The external variable contains elapsed time, output position and the original
three primary parameters (`app:ch_response:lem:energy-carrier-jets`). -/
def elapsedStationarySystem
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (φ : Euclidean (d + 1) → Euclidean 3 → ℝ)
    (v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) ×
      (Euclidean (d + 1) × Euclidean (d + 1))) :
    Euclidean (d + 1) × Euclidean (d + 1) :=
  (gradient (fun z ↦ φ z v.1.2.2) v.2.1 - v.2.2,
    elapsedInputBase C v.1.1 v.1.2.1 v.2.2 - v.2.1)

/-- The diagonal stationary Jacobian `(a,b) ↦ (Aa-b,-a)` is invertible
for every primary Hessian `A`; no bound or gap is postulated
(`app:ch_response:lem:energy-carrier-jets`). -/
def stationaryDiagonalEquiv (A : Euclidean (d + 1) →L[ℝ] Euclidean (d + 1)) :
    (Euclidean (d + 1) × Euclidean (d + 1)) ≃L[ℝ]
      (Euclidean (d + 1) × Euclidean (d + 1)) where
  toLinearEquiv := {
    toLinearMap := (((A.comp (ContinuousLinearMap.fst ℝ _ _)) - ContinuousLinearMap.snd ℝ _ _).prod
      (-ContinuousLinearMap.fst ℝ _ _)).toLinearMap
    invFun := fun w ↦ (-w.2, -A w.2 - w.1)
    left_inv := by intro w; ext <;> simp
    right_inv := by intro w; ext <;> simp }
  continuous_toFun := ((A.continuous.comp continuous_fst).sub continuous_snd).prodMk
    continuous_fst.neg
  continuous_invFun := continuous_snd.neg.prodMk
    ((A.continuous.comp continuous_snd).neg.sub continuous_fst)

/-- Evaluation of the explicit diagonal stationary Jacobian
(`app:ch_response:lem:energy-carrier-jets`). -/
@[simp] theorem stationaryDiagonalEquiv_apply
    (A : Euclidean (d + 1) →L[ℝ] Euclidean (d + 1))
    (w : Euclidean (d + 1) × Euclidean (d + 1)) :
    stationaryDiagonalEquiv A w = (A w.1 - w.2, -w.1) := rfl

private theorem contDiff_elapsedChartPoint :
    ContDiff ℝ ∞ (fun v : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) ↦
      elapsedChartPoint v.1 v.2.1 v.2.2) := by
  unfold elapsedChartPoint
  fun_prop

/-- The actual inverse chart makes the stationary system jointly smooth.
The gradient regularity is supplied by the SAME primary chart, for example
`carrierGradient_smooth` (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffAt_elapsedStationarySystem
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {r : ℝ} {x z θ : Euclidean (d + 1)} {c : Euclidean 3}
    (hC : ContDiffAt ℝ ∞ C.symm (elapsedChartPoint r x θ))
    (hg : ContDiffAt ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) (z, c)) :
    ContDiffAt ℝ ∞ (elapsedStationarySystem C φ) ((r, (x, c)), (z, θ)) := by
  have hp := contDiff_elapsedChartPoint.contDiffAt.comp
    (x := ((r, (x, c)), (z, θ)))
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk contDiffAt_snd.snd))
  have hb := hC.comp (x := ((r, (x, c)), (z, θ))) hp
  have ht : ContDiffAt ℝ ∞
      (fun v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) ×
        (Euclidean (d + 1) × Euclidean (d + 1)) ↦ v.1.2.1 0 - v.1.1)
      ((r, (x, c)), (z, θ)) := by fun_prop
  exact ((hg.comp ((r, (x, c)), (z, θ)) (contDiffAt_snd.fst.prodMk contDiffAt_fst.snd.snd)).sub
    contDiffAt_snd.snd).prodMk
      ((timeSpacePointCLM.contDiff.contDiffAt.comp _ (ht.prodMk hb.snd.snd.fst)).sub
        contDiffAt_snd.fst)

/-- At elapsed time zero the partial stationary derivative is the explicit
invertible block operator. The zero-time base identity is derived above from
the actual flow (`app:ch_response:lem:energy-carrier-jets`). -/
theorem elapsedStationarySystem_partial_isInvertible
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {w₀ : RootState (Euclidean d)} {R ε : ℝ}
    (hsource : C.source ⊆ twoTimeDomain w₀ R ε)
    (hi : ∀ w ∈ ball w₀ R, Φ (w, 0) = w)
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {x θ : Euclidean (d + 1)} {c : Euclidean 3}
    (hq : elapsedChartPoint 0 x θ ∈ C.target)
    (hs : ContDiffAt ℝ ∞ C.symm (elapsedChartPoint 0 x θ))
    (hg : ContDiffAt ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) (x, c)) :
    (fderiv ℝ (elapsedStationarySystem C φ) ((0, (x, c)), (x, θ)) ∘L
      .inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
        (Euclidean (d + 1) × Euclidean (d + 1))).IsInvertible := by
  have hf := (contDiffAt_elapsedStationarySystem hs hg).differentiableAt (by simp)
  have hg' := (hg.comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  let A := fderiv ℝ (gradient (fun z ↦ φ z c)) x
  have he : (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
      elapsedStationarySystem C φ ((0, (x, c)), w)) =ᶠ[𝓝 (x, θ)]
      (fun w ↦ (gradient (fun z ↦ φ z c) w.1 - w.2, x - w.1)) := by
    have hc : ContinuousAt (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
        elapsedChartPoint 0 x w.2) (x, θ) := by
      exact contDiff_elapsedChartPoint.continuous.continuousAt.comp
        (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_snd))
    filter_upwards [hc.preimage_mem_nhds (C.open_target.mem_nhds hq)] with w hw
    simp only [elapsedStationarySystem, elapsedInputBase_zero hC hsource hi hw]
  have hd : HasFDerivAt (fun w : Euclidean (d + 1) × Euclidean (d + 1) ↦
      (gradient (fun z ↦ φ z c) w.1 - w.2, x - w.1))
      (stationaryDiagonalEquiv A).toContinuousLinearMap (x, θ) := by
    convert! ((hg'.hasFDerivAt.comp (x, θ) (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt).sub
      (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) x (x, θ)).sub (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt) using 1
    ext w <;> simp [stationaryDiagonalEquiv, A, Function.comp_def]
  have hd' := hf.hasFDerivAt.comp (x, θ)
    ((hasFDerivAt_const (𝕜 := ℝ) ((0 : ℝ), (x, c)) (x, θ)).prodMk (hasFDerivAt_id (x, θ)))
  have hid := hd'.unique (hd.congr_of_eventuallyEq he)
  rw [show fderiv ℝ (elapsedStationarySystem C φ) ((0, (x, c)), (x, θ)) ∘L
      .inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
        (Euclidean (d + 1) × Euclidean (d + 1)) =
        (stationaryDiagonalEquiv A).toContinuousLinearMap from hid]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Construct one smooth locally unique stationary branch on fixed open
parameter and source/covector neighborhoods. All partial stationary Jacobians
on these neighborhoods are invertible. This supplies actual critical points
for `app:ch_response:lem:energy-carrier-jets`; the remaining global compact
patch and uniform quantitative bounds are not asserted here. -/
theorem exists_elapsedStationary_branch
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {w₀ : RootState (Euclidean d)} {R ε : ℝ}
    (hsource : C.source ⊆ twoTimeDomain w₀ R ε)
    (hi : ∀ w ∈ ball w₀ R, Φ (w, 0) = w)
    (hs : ContDiffOn ℝ ∞ C.symm C.target)
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {Ω : Set (Euclidean (d + 1) × Euclidean 3)} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) Ω)
    {x : Euclidean (d + 1)} {c : Euclidean 3} (hxc : (x, c) ∈ Ω)
    (hq : elapsedChartPoint 0 x (gradient (fun z ↦ φ z c) x) ∈ C.target) :
    ∃ V : Set (ℝ × (Euclidean (d + 1) × Euclidean 3)),
    ∃ B : Set (Euclidean (d + 1) × Euclidean (d + 1)),
    ∃ κ : (ℝ × (Euclidean (d + 1) × Euclidean 3)) →
      Euclidean (d + 1) × Euclidean (d + 1),
      IsOpen V ∧ (0, (x, c)) ∈ V ∧ IsOpen B ∧
      (x, gradient (fun z ↦ φ z c) x) ∈ B ∧ ContDiffOn ℝ ∞ κ V ∧
      κ (0, (x, c)) = (x, gradient (fun z ↦ φ z c) x) ∧ MapsTo κ V B ∧
      ∀ q ∈ V, ∀ w ∈ B,
        (w.1, q.2.2) ∈ Ω ∧ elapsedChartPoint q.1 q.2.1 w.2 ∈ C.target ∧
        (fderiv ℝ (elapsedStationarySystem C φ) (q, w) ∘L
          .inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
            (Euclidean (d + 1) × Euclidean (d + 1))).IsInvertible ∧
        (elapsedStationarySystem C φ (q, w) = 0 ↔ κ q = w) := by
  let q₀ : ℝ × (Euclidean (d + 1) × Euclidean 3) := (0, (x, c))
  let v₀ := (x, gradient (fun z ↦ φ z c) x)
  let F := elapsedStationarySystem C φ
  let J := fun v ↦ fderiv ℝ F v ∘L
    ContinuousLinearMap.inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
      (Euclidean (d + 1) × Euclidean (d + 1))
  have hf : ContDiffAt ℝ ∞ F (q₀, v₀) := contDiffAt_elapsedStationarySystem
    (hs.contDiffAt (C.open_target.mem_nhds hq)) (hg.contDiffAt (hΩ.mem_nhds hxc))
  have hJ : (J (q₀, v₀)).IsInvertible := elapsedStationarySystem_partial_isInvertible
    hC hsource hi hq (hs.contDiffAt (C.open_target.mem_nhds hq))
      (hg.contDiffAt (hΩ.mem_nhds hxc))
  have hzero : F (q₀, v₀) = 0 := by
    simp [F, q₀, v₀, elapsedStationarySystem, elapsedInputBase_zero hC hsource hi hq]
  let κ := hf.implicitFunction (by simp) hJ
  have hκ : ContDiffAt ℝ ∞ κ q₀ := hf.contDiffAt_implicitFunction (by simp) hJ
  have hκ₀ : κ q₀ = v₀ := hf.implicitFunction_apply_self (by simp) hJ
  have hloc : ∀ᶠ v in 𝓝 (q₀, v₀),
      (v.2.1, v.1.2.2) ∈ Ω ∧ elapsedChartPoint v.1.1 v.1.2.1 v.2.2 ∈ C.target ∧
        (J v).IsInvertible ∧ (F v = 0 ↔ κ v.1 = v.2) := by
    have hpos : ContinuousAt (fun v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) ×
        (Euclidean (d + 1) × Euclidean (d + 1)) ↦ (v.2.1, v.1.2.2)) (q₀, v₀) := by fun_prop
    have hchart := contDiff_elapsedChartPoint.continuous.continuousAt.comp
      (x := (q₀, v₀))
      (continuousAt_fst.fst.prodMk (continuousAt_fst.snd.fst.prodMk continuousAt_snd.snd))
    have hJcont : ContinuousAt J (q₀, v₀) :=
      (hf.continuousAt_fderiv (by simp)).clm_comp continuousAt_const
    filter_upwards [hpos.preimage_mem_nhds (hΩ.mem_nhds hxc),
      hchart.preimage_mem_nhds (C.open_target.mem_nhds hq),
      hJcont.tendsto.eventually hJ.eventually_nhds,
      hf.eventually_apply_eq_iff_implicitFunction (by simp) hJ] with v hv hc hj he
    exact ⟨hv, hc, hj, by simpa only [hzero] using he⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hloc
  have hnear : ∀ᶠ q in 𝓝 q₀, q ∈ ball q₀ δ ∧ κ q ∈ ball v₀ δ := by
    have hk := hκ.continuousAt.preimage_mem_nhds (ball_mem_nhds (κ q₀) hδ)
    rw [hκ₀] at hk
    exact Filter.Eventually.and (ball_mem_nhds q₀ hδ) hk
  obtain ⟨V, hVsub, hV, hqV⟩ := _root_.eventually_nhds_iff.mp hnear
  have hdata q (hqV : q ∈ V) w (hw : w ∈ ball v₀ δ) :=
    hball (show (q, w) ∈ ball (q₀, v₀) δ by
      rw [← ball_prod_same]; exact ⟨(hVsub q hqV).1, hw⟩)
  have hκeq q (hqV : q ∈ V) : F (q, κ q) = 0 :=
    (hdata q hqV (κ q) (hVsub q hqV).2).2.2.2.mpr rfl
  refine ⟨V, ball v₀ δ, κ, hV, hqV, isOpen_ball, mem_ball_self hδ,
    ?_, hκ₀, (fun q hq ↦ (hVsub q hq).2), hdata⟩
  intro q hq
  have hqdata := hdata q hq (κ q) (hVsub q hq).2
  have hFq : ContDiffAt ℝ ∞ F (q, κ q) := contDiffAt_elapsedStationarySystem
    (hs.contDiffAt (C.open_target.mem_nhds hqdata.2.1))
    (hg.contDiffAt (hΩ.mem_nhds hqdata.1))
  let k := hFq.implicitFunction (by simp) hqdata.2.2.1
  have hk : ContDiffAt ℝ ∞ k q := hFq.contDiffAt_implicitFunction (by simp) hqdata.2.2.1
  have hk₀ : k q = κ q := hFq.implicitFunction_apply_self (by simp) hqdata.2.2.1
  have hkmem : ∀ᶠ p in 𝓝 q, k p ∈ ball v₀ δ := by
    apply hk.continuousAt.preimage_mem_nhds
    rw [hk₀]
    exact isOpen_ball.mem_nhds (hVsub q hq).2
  have heq : κ =ᶠ[𝓝 q] k := by
    filter_upwards [hV.mem_nhds hq, hkmem,
      hFq.eventually_apply_implicitFunction (by simp) hqdata.2.2.1] with p hp hkp hep
    apply (hdata p hp (k p) hkp).2.2.2.mp
    exact hep.trans (hκeq q hq)
  exact (hk.congr_of_eventuallyEq heq).contDiffWithinAt

end JanetCartan.CompatibleResponse
