module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeFlow

/-!
# Liouville conservation with variable source time

The direct phase in `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`,
needs both time identities. For the actual characteristic field
`(1,-h_η,h_y)`, degree-one homogeneity implies preservation of the restricted
Liouville form `h dt + η·dy`. The proof differentiates Euler's identity and
uses the genuine initial-data variational equation supplied by `TwoTimeFlow`.
It retains variations of the initial time and initial covector.

`rootLiouville_twoTimeState` is the input to the phase differential on the
same inverse projection chart. Its flow hypotheses are precisely outputs of
`exists_twoTimeHamiltonFlow`. No phase or canonical identity is assumed.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz evaluation identifies the actual spatial partial derivative
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem inner_rootPositionGradient (h : RootState E → ℝ) (z : RootState E) (v : E) :
    ⟪rootPositionGradient h z, v⟫_ℝ = fderiv ℝ h z (0, (v, 0)) := by
  simp [rootPositionGradient, InnerProductSpace.toDual_symm_apply]

/-- Riesz evaluation identifies the actual covector partial derivative
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem inner_rootMomentumGradient (h : RootState E → ℝ) (z : RootState E) (v : E) :
    ⟪rootMomentumGradient h z, v⟫_ℝ = fderiv ℝ h z (0, (0, v)) := by
  simp [rootMomentumGradient, InnerProductSpace.toDual_symm_apply]

/-- Split the root differential into its physical-time, spatial and covector
parts (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem root_fderiv_split (h : RootState E → ℝ) (z w : RootState E) :
    fderiv ℝ h z w = w.1 * fderiv ℝ h z (1, (0, 0)) +
      ⟪rootPositionGradient h z, w.2.1⟫_ℝ + ⟪rootMomentumGradient h z, w.2.2⟫_ℝ := by
  rw [inner_rootPositionGradient, inner_rootMomentumGradient]
  have he : w = w.1 • (1, (0, 0)) + (0, (w.2.1, 0)) + (0, (0, w.2.2)) := by simp
  conv_lhs => rw [he]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Local degree-one homogeneity implies Euler's identity for the actual root
gradient (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem root_euler {h : RootState E → ℝ} {z : RootState E}
    (hh : DifferentiableAt ℝ h z)
    (hhom : ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z) :
    ⟪z.2.2, rootMomentumGradient h z⟫_ℝ = h z := by
  have hc : HasDerivAt (fun r : ℝ ↦ (z.1, (z.2.1, r • z.2.2))) (0, (0, z.2.2)) 1 := by
    convert! (hasDerivAt_const (1 : ℝ) z.1).prodMk
      ((hasDerivAt_const (1 : ℝ) z.2.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const z.2.2))
    simp
  have hh' : HasFDerivAt h (fderiv ℝ h z) (z.1, (z.2.1, (1 : ℝ) • z.2.2)) := by
    simpa only [one_smul] using hh.hasFDerivAt
  have hd := hh'.comp_hasDerivAt 1 hc
  have heq : (fun r : ℝ ↦ h (z.1, (z.2.1, r • z.2.2))) =ᶠ[𝓝 1]
      (fun r ↦ r * h z) := hhom
  have he := (hd.congr_of_eventuallyEq heq.symm).unique
    ((hasDerivAt_id (1 : ℝ)).mul_const (h z))
  rw [← inner_rootMomentumGradient, real_inner_comm] at he
  simpa only [one_mul] using he

/-- Differentiate Euler's identity with the source-time variation retained.
This cancels the variational terms in `hasDerivAt_rootLiouville_zero`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem root_differentiated_euler {h : RootState E → ℝ} {z : RootState E}
    (hh : DifferentiableAt ℝ h z) (hp : DifferentiableAt ℝ (rootMomentumGradient h) z)
    (heuler : (fun w : RootState E ↦ ⟪w.2.2, rootMomentumGradient h w⟫_ℝ) =ᶠ[𝓝 z] h)
    (v : RootState E) :
    ⟪z.2.2, fderiv ℝ (rootMomentumGradient h) z v⟫_ℝ =
      v.1 * fderiv ℝ h z (1, (0, 0)) + ⟪rootPositionGradient h z, v.2.1⟫_ℝ := by
  have hi := ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ ℝ (E × E)).hasFDerivAt).inner ℝ hp.hasFDerivAt
  have he := (hi.congr_of_eventuallyEq heuler.symm).unique hh.hasFDerivAt
  have hv := congrArg (fun L : RootState E →L[ℝ] ℝ ↦ L v) he
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply] at hv
  change ⟪z.2.2, fderiv ℝ (rootMomentumGradient h) z v⟫_ℝ +
    ⟪v.2.2, rootMomentumGradient h z⟫_ℝ = fderiv ℝ h z v at hv
  rw [root_fderiv_split, real_inner_comm v.2.2] at hv
  linarith

/-- The restriction `h dt + η·dy` of the Liouville form to `τ=h`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def rootLiouville (h : RootState E → ℝ) (z : RootState E) : RootState E →L[ℝ] ℝ :=
  h z • ContinuousLinearMap.fst ℝ ℝ (E × E) +
    (innerSL ℝ z.2.2).comp ((ContinuousLinearMap.fst ℝ E E).comp
      (ContinuousLinearMap.snd ℝ ℝ (E × E)))

omit [CompleteSpace E] in
/-- Evaluate the restricted Liouville form
(`app:ch_regular_base:lem:characteristic-kernel`). -/
@[simp] theorem rootLiouville_apply (h : RootState E → ℝ) (z w : RootState E) :
    rootLiouville h z w = h z * w.1 + ⟪z.2.2, w.2.1⟫_ℝ := rfl

/-- Euler's identity makes the Liouville form vanish on the actual
characteristic field (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootLiouville_vectorField {h : RootState E → ℝ} {z : RootState E}
    (hh : DifferentiableAt ℝ h z)
    (hhom : ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z) :
    rootLiouville h z (rootHamiltonField h z) = 0 := by
  simp only [rootLiouville_apply, rootHamiltonField, mul_one, inner_neg_right,
    root_euler hh hhom, add_neg_cancel]

/-- The Hamilton and variational ODEs preserve the restricted Liouville form.
The cancellation includes variation of time for a time-dependent root
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_rootLiouville_zero {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z)
    {Z V : ℝ → RootState E} {t : ℝ} (ht : Z t ∈ D)
    (hZ : HasDerivAt Z (rootHamiltonField h (Z t)) t)
    (hV : HasDerivAt V (fderiv ℝ (rootHamiltonField h) (Z t) (V t)) t) :
    HasDerivAt (fun u ↦ rootLiouville h (Z u) (V u)) 0 t := by
  have hhd : DifferentiableAt ℝ h (Z t) :=
    (hh.contDiffAt (hD.mem_nhds ht)).differentiableAt (by simp)
  have hfield : DifferentiableAt ℝ (rootHamiltonField h) (Z t) :=
    ((contDiffOn_rootHamiltonField hD hh).contDiffAt (hD.mem_nhds ht)).differentiableAt
      (by simp)
  have hp : DifferentiableAt ℝ (rootMomentumGradient h) (Z t) := by
    convert! hfield.snd.fst.neg using 1
    ext w
    simp [rootHamiltonField]
  have heuler := root_differentiated_euler hhd hp
    (Filter.eventuallyEq_of_mem (hD.mem_nhds ht) fun w hw ↦
      root_euler ((hh.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)) (hhom w hw))
    (V t)
  have hfst : (fderiv ℝ (rootHamiltonField h) (Z t) (V t)).1 = 0 := by
    have he := hfield.hasFDerivAt.fst.unique (hasFDerivAt_const (1 : ℝ) (Z t))
    exact congrArg (fun L : RootState E →L[ℝ] ℝ ↦ L (V t)) he
  have hy : (fderiv ℝ (rootHamiltonField h) (Z t) (V t)).2.1 =
      -fderiv ℝ (rootMomentumGradient h) (Z t) (V t) := by
    have he := hfield.hasFDerivAt.snd.fst.unique hp.hasFDerivAt.neg
    exact congrArg (fun L : RootState E →L[ℝ] E ↦ L (V t)) he
  have henergy : fderiv ℝ h (Z t) (rootHamiltonField h (Z t)) =
      fderiv ℝ h (Z t) (1, (0, 0)) := by
    rw [root_fderiv_split]
    simp [rootHamiltonField, real_inner_comm]
  have hvfst : HasDerivAt (fun u ↦ (V u).1)
      (fderiv ℝ (rootHamiltonField h) (Z t) (V t)).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivAt t hV
  have hvy : HasDerivAt (fun u ↦ (V u).2.1)
      (fderiv ℝ (rootHamiltonField h) (Z t) (V t)).2.1 t :=
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))).hasFDerivAt.comp_hasDerivAt t hV
  have hzp : HasDerivAt (fun u ↦ (Z u).2.2) (rootPositionGradient h (Z t)) t :=
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))).hasFDerivAt.comp_hasDerivAt t hZ
  have hd := ((hhd.hasFDerivAt.comp_hasDerivAt t hZ).mul hvfst).add (hzp.inner ℝ hvy)
  convert! hd using 1
  rw [hfst, hy, henergy, inner_neg_right, heuler]
  ring

/-- Integrate the proved variational conservation law on the actual two-sided
flow interval (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootLiouville_flowInitialDerivative
    {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ r : ℝ in 𝓝 1, h (z.1, (z.2.1, r • z.2.2)) = r * h z)
    {Φ : RootState E × ℝ → RootState E} {z : RootState E} {ε : ℝ} (hε : 0 < ε)
    (hi : Φ (z, 0) = z)
    (hd : ∀ u ∈ Ioo (-ε) ε,
      HasDerivAt (fun v ↦ Φ (z, v)) (rootHamiltonField h (Φ (z, u))) u)
    (hm : ∀ u ∈ Ioo (-ε) ε, Φ (z, u) ∈ D)
    (hJ₀ : ODE.flowInitialDerivative Φ z 0 = ContinuousLinearMap.id ℝ _)
    (hJ : ∀ u ∈ Ioo (-ε) ε, HasDerivAt (ODE.flowInitialDerivative Φ z)
      ((fderiv ℝ (rootHamiltonField h) (Φ (z, u))).comp
        (ODE.flowInitialDerivative Φ z u)) u)
    {u : ℝ} (hu : u ∈ Ioo (-ε) ε) (v : RootState E) :
    rootLiouville h (Φ (z, u)) (ODE.flowInitialDerivative Φ z u v) =
      rootLiouville h z v := by
  have hc := HamiltonPhase.conserved_of_hasDerivAt_zero isOpen_Ioo isPreconnected_Ioo
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)
    (fun t ht ↦ hasDerivAt_rootLiouville_zero hD hh hhom (hm t ht) (hd t ht)
      (V := fun u ↦ ODE.flowInitialDerivative Φ z u v) (by
        simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
          (hJ t ht).clm_apply (hasDerivAt_const t v))) hu
  simpa only [hi, hJ₀, ContinuousLinearMap.id_apply] using hc

/-- Pull back the Liouville form by the constructed two-time flow. The source
time and covector vary freely; this is the conservation identity consumed by
the two-time phase differential. All ODE hypotheses are supplied by
`exists_twoTimeHamiltonFlow`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootLiouville_twoTimeState
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
    {q : TwoTimePoint E} (hq : q ∈ twoTimeDomain z r ε) (v : TwoTimePoint E) :
    rootLiouville h (twoTimeState Φ q) (fderiv ℝ (twoTimeState Φ) q v) =
      rootLiouville h q.2 v.2 := by
  have hdiff : DifferentiableAt ℝ Φ (q.2, q.1 - q.2.1) :=
    (hΦ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hq)).differentiableAt (by simp)
  have hsec := HamiltonPhase.hasFDerivAt_sectionFlow (ι := id) hdiff (hd _ hq.1 _ hq.2)
    (hasFDerivAt_id q.2)
  have hinput := ((ContinuousLinearMap.fst ℝ ℝ (RootState E)).hasFDerivAt.sub
    ((ContinuousLinearMap.fst ℝ ℝ (E × E)).hasFDerivAt.comp q
      (ContinuousLinearMap.snd ℝ ℝ (RootState E)).hasFDerivAt)).prodMk
        (ContinuousLinearMap.snd ℝ ℝ (RootState E)).hasFDerivAt
  have hc := hsec.comp q (show HasFDerivAt
    (fun q : TwoTimePoint E ↦ (q.1 - q.2.1, q.2)) _ q from hinput)
  simp only [id_eq] at hc
  have hzero := rootLiouville_vectorField
    ((hh.contDiffAt (hD.mem_nhds (hm _ hq.1 _ hq.2))).differentiableAt (by simp))
    (hhom _ (hm _ hq.1 _ hq.2))
  change rootLiouville h (twoTimeState Φ q) (fderiv ℝ
    ((fun q : ℝ × RootState E ↦ Φ (q.2, q.1)) ∘
      (fun q : TwoTimePoint E ↦ (q.1 - q.2.1, q.2))) q v) = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    HamiltonPhase.flowDifferential_apply, map_add, map_smul, twoTimeState, hzero,
    smul_zero, zero_add, ContinuousLinearMap.id_apply]
  exact rootLiouville_flowInitialDerivative hD hh hhom hε (hi _ hq.1)
    (hd _ hq.1) (hm _ hq.1) (hJ₀ _ hq.1) (hJ _ hq.1) hq.2 v.2

end JanetCartan.RegularSector.Characteristic
