module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.CommonChart.Projection

/-!
# Differential comparison for the actual inverse chart

Differentiate the inverse equation and retain the small normalized projection
error. The consumer is the Frobenius spatial half-gap of the two-time phase
in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- The inverse differential differs from the explicit diagonal inverse
shear by the normalized projection error times the inverse Lipschitz bound.
All inputs are supplied by `exists_common_twoTimeProjectionChart`; this
estimate is used to choose its tolerance for the actual spatial mixed gap
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_fderiv_twoTimeChart_symm_sub_shear_le
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {z : RootState E} {R r T δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (hsource : C.source ⊆ twoTimeDomain z r T)
    (hinv : ContDiffOn ℝ ∞ C.symm C.target)
    (hgap : ∀ x ∈ C.source,
      ‖(twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap.comp
        (fderiv ℝ (twoTimeProjection Φ) x) -
          ContinuousLinearMap.id ℝ (TwoTimePoint E)‖ ≤ δ)
    (hlip : ∀ q ∈ C.target, ∀ q' ∈ C.target,
      ‖C.symm q - C.symm q'‖ ≤ L * ‖q - q'‖)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    ‖fderiv ℝ C.symm q -
      (twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap‖ ≤ δ * L := by
  let A := (twoTimeProjectionEquiv (-rootMomentumGradient h z)).symm.toContinuousLinearMap
  let B := fderiv ℝ (twoTimeProjection Φ) (C.symm q)
  let J := fderiv ℝ C.symm q
  have hJ : ‖J‖ ≤ L := norm_fderiv_le_of_lipschitzOn ℝ
    (C.open_target.mem_nhds hq)
    (show LipschitzOnWith ⟨L, hL⟩ C.symm C.target from
      lipschitzOnWith_iff_norm_sub_le.mpr hlip)
  have hi := ((hinv.contDiffAt (C.open_target.mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt
  have hf := (((rootFlow_twoTimeProjection_smooth hΦ).contDiffAt
    ((isOpen_twoTimeDomain z r T).mem_nhds
      (hsource (C.map_target hq)))).differentiableAt (by simp)).hasFDerivAt
  have he : (fun w ↦ twoTimeProjection Φ (C.symm w)) =ᶠ[𝓝 q] id := by
    filter_upwards [C.eventually_right_inverse hq] with w hw
    exact hC ▸ hw
  have hBJ : B.comp J = ContinuousLinearMap.id ℝ (TwoTimePoint E) := by
    have hc := (hf.comp q hi).fderiv
    change fderiv ℝ (fun w ↦ twoTimeProjection Φ (C.symm w)) q = B.comp J at hc
    rw [he.fderiv_eq, fderiv_id] at hc
    exact hc.symm
  have hid : (A.comp B - ContinuousLinearMap.id ℝ (TwoTimePoint E)).comp J = A - J := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hBJ,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  change ‖J - A‖ ≤ δ * L
  rw [norm_sub_rev, ← hid]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hgap _ (C.map_target hq)) hJ (norm_nonneg _) hδ)

end JanetCartan.RegularSector.Characteristic
