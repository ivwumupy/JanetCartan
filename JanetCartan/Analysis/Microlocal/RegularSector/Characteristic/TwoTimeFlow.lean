module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalFlow
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Two-time flow for the direct characteristic kernel

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, the root
Hamiltonian `h(t,y,η)` determines the autonomized field `(1,-h_η,h_y)`.
Its spatial derivatives are the actual Riesz representatives of `fderiv h`.
Picard–Lindelöf constructs one smooth local flow, and evaluation at elapsed
time `t-s` gives joint dependence on both times, with the exact clock,
diagonal data, and variational equation retained.

The consumer is `TwoTimeChart`, which constructs the inverse projection used
by the phase and signed row transport. Only smoothness of the scalar root on
an open domain is an input here; no flow, phase, or inverse is assumed.
This local result does not supply the common coefficient-family buffers or
symbol budgets required for the full regular-sector theorem.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Source time, spatial position, and spatial covector for the characteristic
flow (`app:ch_regular_base:lem:characteristic-kernel`). -/
abbrev RootState (E : Type*) := ℝ × (E × E)

/-- Output time followed by source time, initial position, and initial
covector (`app:ch_regular_base:lem:characteristic-kernel`). -/
abbrev TwoTimePoint (E : Type*) := ℝ × RootState E

/-- The actual spatial gradient of the simple root
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootPositionGradient (h : RootState E → ℝ) (z : RootState E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ h z).comp
    ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E)))

/-- The actual momentum gradient of the simple root
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootMomentumGradient (h : RootState E → ℝ) (z : RootState E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ h z).comp
    ((ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E)))

/-- Autonomization of the characteristic equations for `Ψ_t = h(t,y,Ψ_y)`:
`(t,y,η)′ = (1,-h_η,h_y)`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootHamiltonField (h : RootState E → ℝ) (z : RootState E) : RootState E :=
  (1, (-rootMomentumGradient h z, rootPositionGradient h z))

/-- Root smoothness supplies the actual field smoothness needed by the ODE
constructor (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_rootHamiltonField {h : RootState E → ℝ}
    {D : Set (RootState E)} (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D) :
    ContDiffOn ℝ ∞ (rootHamiltonField h) D := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ h) D :=
    hh.fderiv_of_isOpen hD (by simp)
  have hy := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hd.clm_comp (contDiffOn_const (c :=
      (ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inl ℝ E E))))
  have hp := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hd.clm_comp (contDiffOn_const (c :=
      (ContinuousLinearMap.inr ℝ ℝ (E × E)).comp (ContinuousLinearMap.inr ℝ E E))))
  exact contDiffOn_const.prodMk (hp.neg.prodMk hy)

/-- The joint two-time domain of the reparameterized local flow
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeDomain (z : RootState E) (r ε : ℝ) : Set (TwoTimePoint E) :=
  {q | q.2 ∈ ball z r ∧ q.1 - q.2.1 ∈ Ioo (-ε) ε}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The flow domain is open jointly in both times and the initial state
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem isOpen_twoTimeDomain (z : RootState E) (r ε : ℝ) :
    IsOpen (twoTimeDomain z r ε) :=
  (isOpen_ball.preimage continuous_snd).inter
    (isOpen_Ioo.preimage (continuous_fst.sub continuous_snd.fst))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every allowed initial state occurs on the interior time diagonal
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem diagonal_mem_twoTimeDomain {z : RootState E} {r ε : ℝ}
    (hε : 0 < ε) {w : RootState E} (hw : w ∈ ball z r) :
    (w.1, w) ∈ twoTimeDomain z r ε :=
  ⟨hw, by simpa using (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)⟩

/-- Evaluate the same autonomous flow at elapsed time `t-s`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeState (Φ : RootState E × ℝ → RootState E) (q : TwoTimePoint E) : RootState E :=
  Φ (q.2, q.1 - q.2.1)

/-- At `t=s`, the full variation is `δz + (δt-δs)V(z)`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeStateDiagonalDifferential (v : RootState E) :
    TwoTimePoint E →L[ℝ] RootState E :=
  ContinuousLinearMap.snd ℝ ℝ (RootState E) +
    (ContinuousLinearMap.fst ℝ ℝ (RootState E) -
      (ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
        (ContinuousLinearMap.snd ℝ ℝ (RootState E))).smulRight v

omit [CompleteSpace E] in
/-- Evaluation of the diagonal variation, retaining the source-time term
(`app:ch_regular_base:lem:characteristic-kernel`). -/
@[simp] theorem twoTimeStateDiagonalDifferential_apply (v : RootState E) (w : TwoTimePoint E) :
    twoTimeStateDiagonalDifferential v w = w.2 + (w.1 - w.2.1) • v := rfl

omit [CompleteSpace E] in
/-- Derive the two-time diagonal differential from the actual initial-data
and time derivatives of the ODE flow. This is the invertibility input of
`exists_twoTimeProjectionChart`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_twoTimeState_diagonal {Φ : RootState E × ℝ → RootState E}
    {z v : RootState E} (hΦ : DifferentiableAt ℝ Φ (z, 0))
    (hd : HasDerivAt (fun u ↦ Φ (z, u)) v 0)
    (hJ : ODE.flowInitialDerivative Φ z 0 = ContinuousLinearMap.id ℝ _) :
    HasFDerivAt (twoTimeState Φ) (twoTimeStateDiagonalDifferential v) (z.1, z) := by
  have ha := HamiltonPhase.hasFDerivAt_sectionFlow (ι := id) hΦ hd (hasFDerivAt_id z)
  have hi := ((ContinuousLinearMap.fst ℝ ℝ (RootState E)).hasFDerivAt.sub
    ((ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp (z.1, z)
      (ContinuousLinearMap.snd ℝ ℝ (RootState E)).hasFDerivAt)).prodMk
        (ContinuousLinearMap.snd ℝ ℝ (RootState E)).hasFDerivAt
  have ha' : HasFDerivAt (fun q : ℝ × RootState E ↦ Φ (q.2, q.1))
      (HamiltonPhase.flowDifferential v (ODE.flowInitialDerivative Φ z 0))
      (z.1 - z.1, z) := by simpa only [sub_self, id_eq, ContinuousLinearMap.comp_id] using ha
  have hc := ha'.comp (z.1, z) (show HasFDerivAt
    (fun q : TwoTimePoint E ↦ (q.1 - q.2.1, q.2)) _ (z.1, z) from hi)
  convert! hc using 1
  apply ContinuousLinearMap.ext
  intro w
  simp [twoTimeStateDiagonalDifferential, HamiltonPhase.flowDifferential, hJ, add_comm]

/-- Construct the smooth two-time characteristic flow from the scalar root.
The same flow has the exact physical clock, diagonal data, Hamilton equations,
and initial-state variational equation on one open joint domain. No solution
or inverse is supplied as a hypothesis
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_twoTimeHamiltonFlow {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D) {z : RootState E} (hz : z ∈ D) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : RootState E × ℝ → RootState E,
      ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-ε) ε) ∧
      (∀ w ∈ ball z r, Φ (w, 0) = w) ∧
      (∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (fun v ↦ Φ (w, v)) (rootHamiltonField h (Φ (w, u))) u) ∧
      (∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε, Φ (w, u) ∈ D) ∧
      (∀ w ∈ ball z r, ODE.flowInitialDerivative Φ w 0 = ContinuousLinearMap.id ℝ _) ∧
      (∀ w ∈ ball z r, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (ODE.flowInitialDerivative Φ w)
          ((fderiv ℝ (rootHamiltonField h) (Φ (w, u))).comp
            (ODE.flowInitialDerivative Φ w u)) u) ∧
      ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z r ε) ∧
      (∀ q ∈ twoTimeDomain z r ε, twoTimeState Φ q ∈ D ∧ (twoTimeState Φ q).1 = q.1) ∧
      (∀ w ∈ ball z r, twoTimeState Φ (w.1, w) = w) ∧
      (∀ q ∈ twoTimeDomain z r ε,
        HasDerivAt (fun t ↦ twoTimeState Φ (t, q.2))
          (rootHamiltonField h (twoTimeState Φ q)) q.1) := by
  obtain ⟨r, hr, ε, hε, Φ, hΦ, _, hi, hd, hm, hJ₀, hJ, _⟩ :=
    ODE.exists_contDiffOn_localFlow_in_open (⊤ : ℕ∞) (by simp) hD hz
      (contDiffOn_rootHamiltonField hD hh) 0
  simp only [zero_sub, zero_add] at hΦ hd hm hJ
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hclock (w : RootState E) (hw : w ∈ ball z r) (u : ℝ) (hu : u ∈ Ioo (-ε) ε) :
      (Φ (w, u)).1 = w.1 + u := by
    have hc := HamiltonPhase.conserved_of_hasDerivAt_zero isOpen_Ioo isPreconnected_Ioo hzero
      (f := fun v ↦ (Φ (w, v)).1 - v)
      (fun v hv ↦ by
        have hx := (ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivAt v
          (hd w (ball_subset_closedBall hw) v hv)
        have hx' : HasDerivAt (fun v ↦ (Φ (w, v)).1) 1 v := hx
        convert! hx'.sub (hasDerivAt_id v) using 1
        norm_num) hu
    rw [hi w (ball_subset_closedBall hw)] at hc
    simpa only [sub_zero] using (sub_eq_iff_eq_add.mp hc)
  have htwo : ContDiffOn ℝ ∞ (twoTimeState Φ) (twoTimeDomain z r ε) :=
    hΦ.comp (contDiffOn_snd.prodMk (contDiffOn_fst.sub contDiffOn_snd.fst))
      (fun _ hq ↦ hq)
  refine ⟨r, hr, ε, hε, Φ, hΦ, (fun w hw ↦ hi w (ball_subset_closedBall hw)),
    (fun w hw ↦ hd w (ball_subset_closedBall hw)),
    (fun w hw u hu ↦ hm w (ball_subset_closedBall hw) u (Ioo_subset_Icc_self hu)),
    hJ₀, hJ, htwo, ?_, ?_, ?_⟩
  · intro q hq
    refine ⟨hm q.2 (ball_subset_closedBall hq.1) _ (Ioo_subset_Icc_self hq.2), ?_⟩
    dsimp only [twoTimeState]
    rw [hclock q.2 hq.1 _ hq.2]
    ring
  · intro w hw
    simpa only [twoTimeState, sub_self] using hi w (ball_subset_closedBall hw)
  · intro q hq
    have ht := (hd q.2 (ball_subset_closedBall hq.1) _ hq.2).scomp q.1
      ((hasDerivAt_id q.1).sub_const q.2.1)
    simpa only [one_smul, twoTimeState, Function.comp_def, id_eq] using ht

end JanetCartan.RegularSector.Characteristic
