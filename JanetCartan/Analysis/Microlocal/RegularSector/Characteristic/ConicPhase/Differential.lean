module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Locality

/-!
# Derivatives and both time identities of the conic phase

The covector derivative has no radial correction: the original phase's
Euler identity cancels that correction exactly. Physical gradients and
both time derivatives are the appropriately scaled derivatives of the same
local phase. Root homogeneity then gives both eikonal identities.
Source: `app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (ℓ : E →L[ℝ] ℝ) {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)} {q : TwoTimePoint E}
    (hdiff : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (normalize ℓ q)) (normalize ℓ q))
include hdiff

/-- The continued output-time derivative, before applying root homogeneity.
The local differential is supplied by `exists_buffered_physical_pencil_kernel`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_phase_outputTime : HasDerivAt (fun t ↦ phase ℓ C (t, q.2))
    (ℓ q.2.2.2 * h (q.1, (q.2.2.1, (twoTimeState Φ (C.symm (normalize ℓ q))).2.2))) q.1 := by
  exact (hasDerivAt_twoTimePhase_outputTime hdiff).const_mul (ℓ q.2.2.2)

/-- The continued source-time derivative retains its negative sign
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_phase_sourceTime : HasDerivAt (fun s ↦ phase ℓ C (q.1, (s, q.2.2)))
    (-(ℓ q.2.2.2 * h (q.2.1, ((C.symm (normalize ℓ q)).2.2.1,
      (normalize ℓ q).2.2.2)))) q.2.1 := by
  simpa only [phase, extend, normalize, mul_neg] using
    (hasDerivAt_twoTimePhase_sourceTime hdiff).const_mul (ℓ q.2.2.2)

/-- The physical differential is the positively scaled momentum of the
same local flow (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_phase_position : HasFDerivAt (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2))))
    (innerSL ℝ (ℓ q.2.2.2 • (twoTimeState Φ (C.symm (normalize ℓ q))).2.2)) q.2.2.1 := by
  convert! (hasFDerivAt_twoTimePhase_position hdiff).const_mul (ℓ q.2.2.2) using 1
  ext v
  simp

/-- The covector differential is the same local footpoint at the normalized
covector. The radial correction vanishes by the original phase's Euler
identity (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_phase_covector (hℓ : ℓ q.2.2.2 ≠ 0) :
    HasFDerivAt (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η))))
      (innerSL ℝ (C.symm (normalize ℓ q)).2.2.1) q.2.2.2 := by
  have hn := ((hasFDerivAt_inv hℓ).comp q.2.2.2 ℓ.hasFDerivAt).smul
    (hasFDerivAt_id q.2.2.2)
  have hf : HasFDerivAt (fun θ : E ↦ twoTimePhase C (q.1, (q.2.1, (q.2.2.1, θ))))
      (innerSL ℝ (C.symm (normalize ℓ q)).2.2.1) ((ℓ q.2.2.2)⁻¹ • q.2.2.2) :=
    hasFDerivAt_twoTimePhase_covector hdiff
  have he := ℓ.hasFDerivAt.mul (hf.comp (f := fun η : E ↦ (ℓ η)⁻¹ • η) q.2.2.2 hn)
  convert! he using 1
  ext v
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, smul_eq_mul, twoTimePhase, normalize, Function.comp_apply,
    id_eq, inner_add_right, inner_smul_right]
  field_simp
  ring

/-- The literal physical gradient of the constructed conic phase
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem gradient_phase_position [CompleteSpace E] :
    gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1 =
      ℓ q.2.2.2 • (twoTimeState Φ (C.symm (normalize ℓ q))).2.2 :=
  (show HasGradientAt _ _ _ from hasFDerivAt_phase_position ℓ hdiff).gradient

/-- The literal initial-covector gradient of the constructed conic phase
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem gradient_phase_covector [CompleteSpace E] (hℓ : ℓ q.2.2.2 ≠ 0) :
    gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2 =
      (C.symm (normalize ℓ q)).2.2.1 :=
  (show HasGradientAt _ _ _ from hasFDerivAt_phase_covector ℓ hdiff hℓ).gradient

/-- Both continued Hamilton–Jacobi identities for the SAME root `h`.
The precise root-scaling premise is the last conclusion of
`exists_pencilRoot_domain` in `PencilRoot.lean`. Its domain and homogeneity
must be retained through the parent's
same root/minor/flow witness. The two domain memberships concern only the
normalized local initial and final states; no extended eikonal identity is
assumed (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem phase_eikonal_identities [CompleteSpace E]
    {D : Set (RootState E)}
    (hroot : ∀ w ∈ D, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ D ∧ h (w.1, (w.2.1, a • w.2.2)) = a * h w)
    (hout : (q.1, (q.2.2.1, (twoTimeState Φ (C.symm (normalize ℓ q))).2.2)) ∈ D)
    (hsource : (q.2.1, ((C.symm (normalize ℓ q)).2.2.1, (normalize ℓ q).2.2.2)) ∈ D)
    (hℓ : 0 < ℓ q.2.2.2) :
    deriv (fun t ↦ phase ℓ C (t, q.2)) q.1 =
      h (q.1, (q.2.2.1, gradient (fun y ↦ phase ℓ C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1)) ∧
    -deriv (fun s ↦ phase ℓ C (q.1, (s, q.2.2))) q.2.1 =
      h (q.2.1, (gradient (fun η ↦ phase ℓ C (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2, q.2.2.2)) := by
  rw [gradient_phase_position ℓ hdiff, gradient_phase_covector ℓ hdiff hℓ.ne',
    (hasDerivAt_phase_outputTime ℓ hdiff).deriv,
    (hasDerivAt_phase_sourceTime ℓ hdiff).deriv, neg_neg]
  constructor
  · exact (hroot _ hout _ hℓ).2.symm
  · have he := (hroot _ hsource _ hℓ).2
    simpa only [normalize, smul_inv_smul₀ hℓ.ne'] using he.symm

omit hdiff [InnerProductSpace ℝ E] in
/-- The original transport buffer already supplies both local root-domain
memberships used by `phase_eikonal_identities`. The final state comes from
`exists_buffered_physical_pencil_kernel`'s flow-domain conclusion; the initial
state comes from its diagonal identity. Thus no new analytic membership
premise is needed when assembling that consumer
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem root_states_mem_of_transport_buffer {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    {D : Set (RootState E)} {I : Set ℝ} {U : Set (E × E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (hstate : ∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
      (twoTimeState Φ (C.symm q)).1 = q.1)
    (hdiag : ∀ w ∈ I ×ˢ U, (w.1, w) ∈ C.target ∧
      twoTimeState Φ (C.symm (w.1, w)) = w)
    {q : TwoTimePoint E} (hq : q ∈ C.target) (hi : (C.symm q).2 ∈ I ×ˢ U) :
    (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) ∈ D ∧
      (q.2.1, ((C.symm q).2.2.1, q.2.2.2)) ∈ D := by
  have hc := twoTimeChart_inverse_coordinates hC hq
  have ho := hstate q hq
  constructor
  · have he : (q.1, (q.2.2.1, (twoTimeState Φ (C.symm q)).2.2)) =
        twoTimeState Φ (C.symm q) := by
      rw [← ho.2, ← hc.2.2.2]
    exact he ▸ ho.1
  · have hd := hdiag (C.symm q).2 hi
    have hm := (hstate _ hd.1).1
    rw [hd.2] at hm
    simpa only [← hc.2.1, ← hc.2.2.1, Prod.eta] using hm

end JanetCartan.RegularSector.Characteristic.ConicPhase
