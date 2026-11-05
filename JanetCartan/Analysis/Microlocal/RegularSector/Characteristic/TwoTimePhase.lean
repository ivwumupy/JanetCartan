module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeChart
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeLiouville
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The local two-time characteristic phase

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, construct
`Ψ(t,s,y,η) = u(t,s,y,η)·η` from the inverse projection of the actual
characteristic flow. Conservation of `h dt + η·dy` gives the full differential

`dΨ = h(t,y,p) dt - h(s,u,η) ds + p·dy + u·dη`.

Thus both Hamilton–Jacobi time identities hold, including the initial-time
identity needed for the retarded canonical relation. The phase is jointly
smooth in both times and has the exact diagonal data. The existence theorem
constructs the flow and inverse from a smooth locally homogeneous scalar root;
it does not assume a phase, inverse chart, or Liouville identity.

This closes local phase existence for a fixed root. The actual reduced pencil's
root, common coefficient-neighborhood buffers, conic extension and uniform jet
budgets still have to be instantiated in the finite sector construction. No
amplitude estimate, integrated residual identity, or sector Sobolev bound is
asserted here.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The explicit phase using the initial spatial footpoint of the same
inverse chart (`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimePhase (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E))
    (q : TwoTimePoint E) : ℝ := ⟪(C.symm q).2.2.1, q.2.2.2⟫_ℝ

/-- The full expected differential, retaining both Hamiltonian time terms.
`hasFDerivAt_twoTimePhase` proves this formula from the actual flow
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimePhaseDifferential (h : RootState E → ℝ)
    (Φ : RootState E × ℝ → RootState E)
    (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)) (q : TwoTimePoint E) :
    TwoTimePoint E →L[ℝ] ℝ :=
  let u := (C.symm q).2.2.1
  let p := (twoTimeState Φ (C.symm q)).2.2
  let t := ContinuousLinearMap.fst ℝ ℝ (RootState E)
  let s := (ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (RootState E))
  let yp := (ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (RootState E))
  h (q.1, (q.2.2.1, p)) • t - h (q.2.1, (u, q.2.2.2)) • s +
    (innerSL ℝ p).comp ((ContinuousLinearMap.fst ℝ E E).comp yp) +
    (innerSL ℝ u).comp ((ContinuousLinearMap.snd ℝ E E).comp yp)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The inverse retains both times and the initial covector, while its
spatial projection returns the requested physical point
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeChart_inverse_coordinates
    {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    (C.symm q).1 = q.1 ∧ (C.symm q).2.1 = q.2.1 ∧
      (C.symm q).2.2.2 = q.2.2.2 ∧ (twoTimeState Φ (C.symm q)).2.1 = q.2.2.1 := by
  have he := C.right_inv hq
  rw [hC] at he
  dsimp only [twoTimeProjection] at he
  have ht := congrArg (fun w : TwoTimePoint E ↦ w.1) he
  have hs := congrArg (fun w : TwoTimePoint E ↦ w.2.1) he
  have hη := congrArg (fun w : TwoTimePoint E ↦ w.2.2.2) he
  have hy := congrArg (fun w : TwoTimePoint E ↦ w.2.2.1) he
  exact ⟨ht, hs, hη, hy⟩

/-- Derive the full phase differential by pulling the proved Liouville
conservation law through the actual inverse projection. In particular, the
source-time term is derived from the variational ODE rather than assumed.
The ODE and inverse hypotheses are supplied by `exists_twoTimeHamiltonFlow`
and `exists_twoTimeProjectionChart`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_twoTimePhase
    {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z)
    {Φ : RootState E × ℝ → RootState E} {z : RootState E} {r ε : ℝ} (hε : 0 < ε)
    (hΦ : ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-ε) ε))
    (hi : ∀ w ∈ ball z r, Φ (w, 0) = w)
    (hd : ∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε,
      HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u)
    (hm : ∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε, Φ (w, u) ∈ D)
    (hJ₀ : ∀ w ∈ ball z r, ODE.flowInitialDerivative Φ w 0 = ContinuousLinearMap.id ℝ _)
    (hJ : ∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε,
      HasDerivAt (ODE.flowInitialDerivative Φ w)
        ((fderiv ℝ (rootHamiltonField h) (Φ (w, u))).comp
          (ODE.flowInitialDerivative Φ w u)) u)
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (hsource : C.source ⊆ twoTimeDomain z r ε)
    (hclock : ∀ q ∈ twoTimeDomain z r ε, (twoTimeState Φ q).1 = q.1)
    (hCsmooth : ContDiffOn ℝ ∞ C.symm C.target)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q := by
  have hstate : ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z r ε) :=
    hΦ.comp (contDiffOn_snd.prodMk (contDiffOn_fst.sub contDiffOn_snd.fst))
      (fun _ hq ↦ hq)
  have hR := ((hCsmooth.contDiffAt (C.open_target.mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt
  have hs := hsource (C.map_target hq)
  have hZ := ((hstate.contDiffAt ((isOpen_twoTimeDomain z r ε).mem_nhds hs)).differentiableAt
    (by simp)).hasFDerivAt.comp q hR
  have hcoords (w : TwoTimePoint E) (hw : w ∈ C.target) :=
    twoTimeChart_inverse_coordinates hC hw
  have hcl (w : TwoTimePoint E) (hw : w ∈ C.target) :
      (twoTimeState Φ (C.symm w)).1 = w.1 := by
    rw [hclock _ (hsource (C.map_target hw)), (hcoords w hw).1]
  have hZt := (hZ.fst.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (C.open_target.mem_nhds hq) hcl).symm).unique
      (ContinuousLinearMap.fst ℝ ℝ (RootState E)).hasFDerivAt
  have hZy := (hZ.snd.fst.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (C.open_target.mem_nhds hq)
      (fun w hw ↦ (hcoords w hw).2.2.2)).symm).unique
      (((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
          (ContinuousLinearMap.snd ℝ ℝ (RootState E)))).hasFDerivAt)
  have hRs := (hR.snd.fst.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (C.open_target.mem_nhds hq)
      (fun w hw ↦ (hcoords w hw).2.1)).symm).unique
      (((ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
        (ContinuousLinearMap.snd ℝ ℝ (RootState E))).hasFDerivAt)
  have hη := ((ContinuousLinearMap.snd ℝ E E).comp
    ((ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
      (ContinuousLinearMap.snd ℝ ℝ (RootState E)))).hasFDerivAt (x := q)
  have hphase := hR.snd.snd.fst.inner ℝ hη
  convert! hphase using 1
  apply ContinuousLinearMap.ext
  intro v
  have hLv := rootLiouville_twoTimeState hD hh hhom hε hΦ hi hd hm hJ₀ hJ hs
    (fderiv ℝ C.symm q v)
  have htv := congrArg (fun L : TwoTimePoint E →L[ℝ] ℝ ↦ L v) hZt
  have hyv := congrArg (fun L : TwoTimePoint E →L[ℝ] E ↦ L v) hZy
  have hsv := congrArg (fun L : TwoTimePoint E →L[ℝ] ℝ ↦ L v) hRs
  change (fderiv ℝ (twoTimeState Φ) (C.symm q) (fderiv ℝ C.symm q v)).1 = v.1 at htv
  change (fderiv ℝ (twoTimeState Φ) (C.symm q) (fderiv ℝ C.symm q v)).2.1 = v.2.2.1 at hyv
  change (fderiv ℝ C.symm q v).2.1 = v.2.1 at hsv
  rw [rootLiouville_apply, rootLiouville_apply, htv, hyv, hsv,
    (hcoords q hq).2.2.1] at hLv
  have hfinal : twoTimeState Φ (C.symm q) =
      (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) := by
    ext
    · exact hcl q hq
    · exact (hcoords q hq).2.2.2
    · rfl
  have hinitial : (C.symm q).2 = (q.2.1, ((C.symm q).2.2.1, q.2.2.2)) := by
    ext
    · exact (hcoords q hq).2.1
    · rfl
    · exact (hcoords q hq).2.2.1
  rw [hfinal, hinitial] at hLv
  simp only [twoTimePhaseDifferential, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    smul_eq_mul]
  change h (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) * v.1 -
      h (q.2.1, ((C.symm q).2.2.1, q.2.2.2)) * v.2.1 +
      ⟪(twoTimeState Φ (C.symm q)).2.2, v.2.2.1⟫_ℝ +
      ⟪(C.symm q).2.2.1, v.2.2.2⟫_ℝ =
    ⟪(C.symm q).2.2.1, v.2.2.2⟫_ℝ + ⟪(fderiv ℝ C.symm q v).2.2.1, q.2.2.2⟫_ℝ
  have hcomm := real_inner_comm q.2.2.2 (fderiv ℝ C.symm q v).2.2.1
  linarith

omit [CompleteSpace E] in
/-- Joint smoothness of the explicit phase, including the time diagonal
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_twoTimePhase
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : ContDiffOn ℝ ∞ C.symm C.target) : ContDiffOn ℝ ∞ (twoTimePhase C) C.target :=
  hC.snd.snd.fst.inner ℝ contDiffOn_snd.snd.snd

omit [CompleteSpace E] in
/-- The actual initial state and inverse equations give exactly `Ψ(s,s,y,η)=y·η`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimePhase_diagonal {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    {w : RootState E} (hi : Φ (w, 0) = w) (hw : (w.1, w) ∈ C.source) :
    twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ := by
  have hproj : twoTimeProjection Φ (w.1, w) = (w.1, w) := by
    simp [twoTimeProjection, twoTimeState, hi]
  have hinv : C.symm (w.1, w) = (w.1, w) := by
    simpa only [hC, hproj] using C.left_inv hw
  simp only [twoTimePhase, hinv]

omit [CompleteSpace E] in
/-- Output-time Hamilton–Jacobi identity from the proved full differential
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_twoTimePhase_outputTime
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    HasDerivAt (fun t ↦ twoTimePhase C (t, q.2))
      (h (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2))) q.1 := by
  have he := hphase.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  convert! he using 1
  simp [twoTimePhaseDifferential]

omit [CompleteSpace E] in
/-- Initial-time Hamilton–Jacobi identity, with its negative sign, from the
proved full differential (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_twoTimePhase_sourceTime
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    HasDerivAt (fun s ↦ twoTimePhase C (q.1, (s, q.2.2)))
      (-h (q.2.1, ((C.symm q).2.2.1, q.2.2.2))) q.2.1 := by
  have he := hphase.comp_hasDerivAt q.2.1
    ((hasDerivAt_const q.2.1 q.1).prodMk
      ((hasDerivAt_id q.2.1).prodMk (hasDerivAt_const q.2.1 q.2.2)))
  convert! he using 1
  simp [twoTimePhaseDifferential]

omit [CompleteSpace E] in
/-- The physical phase gradient is the covector transported by the same flow
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_twoTimePhase_position
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    HasFDerivAt (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2))))
      (innerSL ℝ (twoTimeState Φ (C.symm q)).2.2) q.2.2.1 := by
  have hx : HasFDerivAt (fun y : E ↦ (q.1, (q.2.1, (y, q.2.2.2)))) _ q.2.2.1 :=
    ((hasFDerivAt_const (𝕜 := ℝ) q.1 q.2.2.1).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) q.2.1 q.2.2.1).prodMk
        ((hasFDerivAt_id (𝕜 := ℝ) q.2.2.1).prodMk
          (hasFDerivAt_const (𝕜 := ℝ) q.2.2.2 q.2.2.1))))
  have he := hphase.comp q.2.2.1 hx
  convert! he using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [twoTimePhaseDifferential]

omit [CompleteSpace E] in
/-- The initial-covector phase gradient is the actual initial footpoint
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_twoTimePhase_covector
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    HasFDerivAt (fun η ↦ twoTimePhase C (q.1, (q.2.1, (q.2.2.1, η))))
      (innerSL ℝ (C.symm q).2.2.1) q.2.2.2 := by
  have hx : HasFDerivAt (fun η : E ↦ (q.1, (q.2.1, (q.2.2.1, η)))) _ q.2.2.2 :=
    ((hasFDerivAt_const (𝕜 := ℝ) q.1 q.2.2.2).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) q.2.1 q.2.2.2).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) q.2.2.1 q.2.2.2).prodMk
          (hasFDerivAt_id (𝕜 := ℝ) q.2.2.2))))
  have he := hphase.comp q.2.2.2 hx
  convert! he using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [twoTimePhaseDifferential]

/-- Both time identities in literal gradient notation:
`Ψ_t=h(t,y,Ψ_y)` and `-Ψ_s=h(s,Ψ_η,η)`. The latter identifies the
source energy of the elapsed-time graph
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem twoTimePhase_eikonal_identities
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hphase : HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    deriv (fun t ↦ twoTimePhase C (t, q.2)) q.1 =
      h (q.1, (q.2.2.1, gradient (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) ∧
    -deriv (fun s ↦ twoTimePhase C (q.1, (s, q.2.2))) q.2.1 =
      h (q.2.1, (gradient (fun η ↦ twoTimePhase C (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2, q.2.2.2)) := by
  have hy : HasGradientAt (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2))))
      (twoTimeState Φ (C.symm q)).2.2 q.2.2.1 := hasFDerivAt_twoTimePhase_position hphase
  have hη : HasGradientAt (fun η ↦ twoTimePhase C (q.1, (q.2.1, (q.2.2.1, η))))
      (C.symm q).2.2.1 q.2.2.2 := hasFDerivAt_twoTimePhase_covector hphase
  rw [hy.gradient, hη.gradient, (hasDerivAt_twoTimePhase_outputTime hphase).deriv,
    (hasDerivAt_twoTimePhase_sourceTime hphase).deriv, neg_neg]
  exact ⟨rfl, rfl⟩

/-- Construct one smooth two-time phase and its actual Hamilton flow and
inverse projection near any point of a smooth locally degree-one root. The
full differential and diagonal data are conclusions. The construction uses
Picard–Lindelöf, the explicit invertible diagonal shear, and the proved
Liouville conservation law. Uniform coefficient-family estimates are not
part of this local theorem
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_localTwoTimeHamiltonPhase
    {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z)
    {z : RootState E} (hz : z ∈ D) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : RootState E × ℝ → RootState E,
      ∃ C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E),
      ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-ε) ε) ∧
      (∀ w ∈ ball z r, Φ (w, 0) = w) ∧
      (∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u) ∧
      (∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε, Φ (w, u) ∈ D) ∧
      ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z r ε) ∧
      (∀ q ∈ twoTimeDomain z r ε, (twoTimeState Φ q).1 = q.1) ∧
      (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ ∧
      C.source ⊆ twoTimeDomain z r ε ∧ (z.1, z) ∈ C.source ∧ (z.1, z) ∈ C.target ∧
      ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target ∧
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
      (∀ w ∈ ball z r, (w.1, w) ∈ C.source → twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) := by
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hi, hd, hm, hJ₀, hJ, hstate, hclock, _, _⟩ :=
    exists_twoTimeHamiltonFlow hD hh hz
  have hbase : z ∈ ball z r := mem_ball_self hr
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hd₀ : HasDerivAt (fun u ↦ Φ (z, u)) (rootHamiltonField h z) 0 := by
    simpa only [hi z hbase] using hd z hbase 0 hzero
  obtain ⟨C, hC, hsource, hzC, hzT, hCf, hCs⟩ :=
    exists_twoTimeProjectionChart hr hε hΦ (hi z hbase) hd₀ (hJ₀ z hbase)
  refine ⟨r, hr, ε, hε, Φ, C, hΦ, hi, hd, hm, hstate,
    (fun q hq ↦ (hclock q hq).2), hC, hsource, hzC, hzT, hCf, hCs,
    contDiffOn_twoTimePhase hCs, ?_, ?_⟩
  · intro q hq
    exact hasFDerivAt_twoTimePhase hD hh hhom hε hΦ hi hd hm hJ₀ hJ hC hsource
      (fun q hq ↦ (hclock q hq).2) hCs hq
  · intro w hw hws
    exact twoTimePhase_diagonal hC (hi w hw) hws

end JanetCartan.RegularSector.Characteristic
