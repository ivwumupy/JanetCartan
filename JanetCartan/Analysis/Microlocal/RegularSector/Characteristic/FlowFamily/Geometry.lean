module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.Flow
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimePhase

/-!
# Two-time geometry of the common Hamilton flow

The flow produced in `FlowFamily.Flow` satisfies the exact identities used by
`app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. These deductions use that same flow,
retain both original times, and include the entire intervening trajectory.
The phase differential is the existing Liouville theorem applied to this flow;
it is not an additional analytic assumption.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
  {z : RootState E} {R r T : ℝ}

/-- The physical clock is derived from the actual autonomous ODE, on the
whole closed time interval and for every allowed initial state
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_clock (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    (hT : 0 < T) {w : RootState E} (hw : w ∈ closedBall z r)
    {u : ℝ} (hu : u ∈ Icc (-T) T) : (Φ (w, u)).1 = w.1 + u := by
  let f : ℝ → ℝ := fun v ↦ (Φ (w, v)).1 - v
  have hd (v : ℝ) (hv : v ∈ Icc (-T) T) :
      HasDerivWithinAt f 0 (Icc (-T) T) v := by
    have hx := (ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivWithinAt v
      (hΦ.ode w hw v hv)
    have hx' : HasDerivWithinAt (fun v ↦ (Φ (w, v)).1) 1 (Icc (-T) T) v := hx
    convert! hx'.sub (hasDerivWithinAt_id v (Icc (-T) T)) using 1
    simp
  have hf (v : ℝ) (hv : v ∈ Icc (-T) T) :
      HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Icc (-T) T) v := by
    simpa using (hd v hv).hasFDerivWithinAt
  have hz : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have he := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (C := 0) hf (by intro v hv; simp) hz hu
  have heq : f u = f 0 := sub_eq_zero.mp (norm_eq_zero.mp (by simpa using he))
  dsimp [f] at heq
  rw [hΦ.initial w hw, sub_zero] at heq
  linarith

/-- Joint smoothness in the two original times follows by the fixed elapsed
time substitution in the common flow
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_twoTimeState_smooth
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ) :
    ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z r T) :=
  hΦ.smooth.comp (contDiffOn_snd.prodMk (contDiffOn_fst.sub contDiffOn_snd.fst))
    (fun _ hq ↦ hq)

/-- The projection of this same flow is jointly smooth
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_twoTimeProjection_smooth
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ) :
    ContDiffOn ℝ ∞ (twoTimeProjection Φ) (twoTimeDomain z r T) :=
  contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk
    ((rootFlow_twoTimeState_smooth hΦ).snd.fst.prodMk contDiffOn_snd.snd.snd))

/-- The reparameterized flow has the exact output clock
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_twoTimeState_clock
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ) (hT : 0 < T)
    {q : TwoTimePoint E} (hq : q ∈ twoTimeDomain z r T) : (twoTimeState Φ q).1 = q.1 := by
  dsimp only [twoTimeState]
  rw [rootFlow_clock hΦ hT (ball_subset_closedBall hq.1) (Ioo_subset_Icc_self hq.2)]
  ring

/-- Every state on the segment between the two original times remains in the
prescribed closed root-state ball, in either orientation. This is the range
input for transport and the retarded canonical relation
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem rootFlow_twoTimeState_segment
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ) (hT : 0 < T)
    {q : TwoTimePoint E} (hq : q ∈ twoTimeDomain z r T)
    {v : ℝ} (hv : v ∈ uIcc q.2.1 q.1) :
    (v, q.2) ∈ twoTimeDomain z r T ∧
      twoTimeState Φ (v, q.2) ∈ closedBall z R ∧ (twoTimeState Φ (v, q.2)).1 = v := by
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hv' : v - q.2.1 ∈ uIcc 0 (q.1 - q.2.1) := by
    rcases le_total q.2.1 q.1 with hle | hle
    · rw [uIcc_of_le hle] at hv
      rw [uIcc_of_le (sub_nonneg.mpr hle)]
      constructor <;> linarith [hv.1, hv.2]
    · rw [uIcc_of_ge hle] at hv
      rw [uIcc_of_ge (sub_nonpos.mpr hle)]
      constructor <;> linarith [hv.1, hv.2]
  have ht := ordConnected_Ioo.uIcc_subset hzero hq.2 hv'
  have hmem : (v, q.2) ∈ twoTimeDomain z r T := ⟨hq.1, ht⟩
  exact ⟨hmem, hΦ.range q.2 (ball_subset_closedBall hq.1) _ (Ioo_subset_Icc_self ht),
    rootFlow_twoTimeState_clock hΦ hT hmem⟩

/-- The actual common flow solves the two-time output-time IVP
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_twoTimeState_hasDerivAt
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    {q : TwoTimePoint E} (hq : q ∈ twoTimeDomain z r T) :
    HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
      (rootHamiltonField h (twoTimeState Φ q)) q.1 := by
  have ht := (hΦ.hasDerivAt (ball_subset_closedBall hq.1) hq.2).scomp q.1
    ((hasDerivAt_id q.1).sub_const q.2.1)
  simpa only [one_smul, twoTimeState, Function.comp_def, id_eq] using ht

/-- On the diagonal the actual state and projection are the identity
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_twoTime_diagonal
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    {w : RootState E} (hw : w ∈ closedBall z r) :
    twoTimeState Φ (w.1, w) = w ∧ twoTimeProjection Φ (w.1, w) = (w.1, w) := by
  simp [twoTimeState, twoTimeProjection, hΦ.initial w hw]

/-- The same common flow and any inverse projection contained in its domain
satisfy the full phase differential, including the negative source-time term.
Every flow, clock and variational premise of the Liouville theorem is discharged
by `IsSmoothFlowOn`; the common inverse constructor supplies the chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootFlow_hasFDerivAt_twoTimePhase
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D)
    (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ w ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ) (hT : 0 < T)
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (hsource : C.source ⊆ twoTimeDomain z r T)
    (hCsmooth : ContDiffOn ℝ ∞ C.symm C.target)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q :=
  hasFDerivAt_twoTimePhase hD hh hhom hT hΦ.smooth
    (fun w hw ↦ hΦ.initial w (ball_subset_closedBall hw))
    (fun _ hw _ ht ↦ hΦ.hasDerivAt (ball_subset_closedBall hw) ht)
    (fun w hw u hu ↦ hRD (hΦ.range w (ball_subset_closedBall hw) u (Ioo_subset_Icc_self hu)))
    hΦ.variation_initial hΦ.variation hC hsource
    (fun _ hq ↦ rootFlow_twoTimeState_clock hΦ hT hq) hCsmooth hq

end JanetCartan.RegularSector.Characteristic
