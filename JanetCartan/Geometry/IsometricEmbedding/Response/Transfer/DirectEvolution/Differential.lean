module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The joint stationary-phase derivative identity

The two segment fundamental-theorem identities and their inverse-Hessian
combination, immediately before `paper-v2.tex`, `new:eq:carrier-ibp`.
The consumer is the original `app:ch_response:eq:direct-envelope-profile`.
All hypotheses below concern the primitive phase, a differentiable critical
point with zero critical value, and invertibility on the same convex box.
The same-primary-phase matching and small-time Hamilton geometry are the
producers of these hypotheses; no kernel estimate is assumed here.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sub_eq_integral_fderiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {g : CarrierVariables n → F} {D : Set (CarrierVariables n)}
    (hD : IsOpen D) (hcD : Convex ℝ D) (hg : ContDiffOn ℝ ∞ g D)
    {v w : CarrierVariables n} (hv : v ∈ D) (hw : w ∈ D) :
    g w - g v = (∫ t in (0 : ℝ)..1, fderiv ℝ g (v + t • (w - v))) (w - v) := by
  have hseg (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : v + t • (w - v) ∈ D :=
    hcD.add_smul_sub_mem hv hw (by simpa using ht)
  have hc : ContinuousOn (fun t : ℝ ↦ fderiv ℝ g (v + t • (w - v))) (uIcc 0 1) := by
    intro t ht
    exact (((hg.fderiv_of_isOpen hD (m := ∞) (by simp)).contDiffAt
      (hD.mem_nhds (hseg t ht))).continuousAt.comp
      (f := fun s : ℝ ↦ v + s • (w - v))
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  rw [ContinuousLinearMap.intervalIntegral_apply hc.intervalIntegrable]
  symm
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ ↦ v + t • (w - v)) (w - v) t := by
    simpa using ((hasDerivAt_id t).smul_const (w - v)).const_add v
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ ((hg.contDiffAt (hD.mem_nhds (hseg t ht))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hpath t))
    (hc.clm_apply continuousOn_const).intervalIntegrable

/-- Differentiating the identically zero critical value proves `∂e f(w₀)=0`;
it is not an additional hypothesis. This is the first step of
`new:eq:carrier-ibp`, for the original direct-envelope consumer. -/
theorem externalDerivative_at_critical_eq_zero
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n} {q : E}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (q, w₀ q))
    (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : gradient (f q) (w₀ q) = 0)
    (hvalue : (fun p ↦ f p (w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0)) (e : E) :
    externalDerivative f e q (w₀ q) = 0 := by
  let D := fderiv ℝ (Function.uncurry f) (q, w₀ q)
  have htotal := hf.hasFDerivAt.comp q ((hasFDerivAt_id q).prodMk hw₀.hasFDerivAt)
  have hzero := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) q).congr_of_eventuallyEq hvalue).fderiv
  have htotalzero : D (e, fderiv ℝ w₀ q e) = 0 := by
    have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L e) (htotal.fderiv.symm.trans hzero)
    simpa [D] using he
  have hsource : fderiv ℝ (f q) (w₀ q) = 0 := by
    have h := congrArg (InnerProductSpace.toDual ℝ (CarrierVariables n)) hcritical
    simpa [gradient] using h
  have hs := (hf.hasFDerivAt.comp (w₀ q) (hasFDerivAt_prodMk_right q (w₀ q))).fderiv
  have hsvalue : D (0, fderiv ℝ w₀ q e) = 0 := by
    have h := congrArg (fun L : CarrierVariables n →L[ℝ] ℝ ↦ L (fderiv ℝ w₀ q e))
      (hs.symm.trans hsource)
    simpa [D] using h
  have hext := (hf.hasFDerivAt.comp q
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q (w₀ q))).fderiv
  simp only [Function.comp_def, Function.uncurry] at hext
  unfold externalDerivative
  rw [hext]
  change D (e, 0) = 0
  have heq : (e, fderiv ℝ w₀ q e) = (e, 0) + (0, fderiv ℝ w₀ q e) := by simp
  rw [heq, map_add, hsvalue, add_zero] at htotalzero
  exact htotalzero

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The gradient equals the averaged Hessian times the displacement from the
same critical point (`new:eq:carrier-ibp`). Convexity supplies the full segment. -/
theorem gradient_eq_averagedPhaseHessian
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {D : Set (CarrierVariables n)} (hD : IsOpen D) (hcD : Convex ℝ D)
    {q : E} (hf : ContDiffOn ℝ ∞ (f q) D)
    {w : CarrierVariables n} (h₀ : w₀ q ∈ D) (hw : w ∈ D)
    (hcritical : gradient (f q) (w₀ q) = 0) :
    gradient (f q) w = averagedPhaseHessian f w₀ q w (w - w₀ q) := by
  have hg : ContDiffOn ℝ ∞ (gradient (f q)) D :=
    (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hD (by simp))
  simpa [averagedPhaseHessian, hcritical] using sub_eq_integral_fderiv hD hcD hg h₀ hw

/-- The external derivative equals the average of its integration-variable
gradient paired with the displacement (`new:eq:carrier-ibp`). -/
theorem externalDerivative_sub_eq_inner_averagedExternalGradient
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {D : Set (CarrierVariables n)} (hD : IsOpen D) (hcD : Convex ℝ D)
    {e q : E} (hf : ContDiffOn ℝ ∞ (externalDerivative f e q) D)
    {w : CarrierVariables n} (h₀ : w₀ q ∈ D) (hw : w ∈ D) :
    externalDerivative f e q w - externalDerivative f e q (w₀ q) =
      inner ℝ (averagedExternalGradient f w₀ e q w) (w - w₀ q) := by
  rw [sub_eq_integral_fderiv hD hcD hf h₀ hw]
  unfold averagedExternalGradient gradient
  have hi : (∫ t in (0 : ℝ)..1, (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm
      (fderiv ℝ (externalDerivative f e q) (w₀ q + t • (w - w₀ q)))) =
      (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm
        (∫ t in (0 : ℝ)..1, fderiv ℝ (externalDerivative f e q)
          (w₀ q + t • (w - w₀ q))) :=
    (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm.toLinearIsometry.intervalIntegral_comp_comm
      (fun t : ℝ ↦ fderiv ℝ (externalDerivative f e q) (w₀ q + t • (w - w₀ q)))
  rw [hi]
  exact InnerProductSpace.toDual_symm_apply.symm

/-- Primitive joint phase smoothness gives smoothness of the actual external
derivative on the supported box (`new:eq:carrier-ibp`). -/
theorem contDiffOn_externalDerivative
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (e : E) :
    ContDiffOn ℝ ∞ (externalDerivative f e q) D := by
  intro w hw
  have hj : ContDiffAt ℝ ∞
      (Function.uncurry (fun w : CarrierVariables n ↦ fun p : E ↦ f p w)) (w, q) :=
    (hf.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hw⟩)).comp (w, q)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  exact ((hj.fderiv (m := ∞) contDiffAt_const (by simp)).clm_apply
    contDiffAt_const).contDiffWithinAt

/-- The constructed inverse-transpose coefficient proves the exact phase
trade `∂e f = A_e · ∇w f` preceding `new:eq:carrier-ibp`. Only primitive joint
phase smoothness, a differentiable zero-valued critical point, and invertibility
of the literal segment average are assumed. This is not yet an integral or
Sobolev estimate for `app:ch_response:eq:direct-envelope-profile`. -/
theorem externalDerivative_eq_inner_transferCoefficient
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : gradient (f q) (w₀ q) = 0)
    (hvalue : (fun p ↦ f p (w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0))
    {w : CarrierVariables n} (h₀ : w₀ q ∈ D) (hw : w ∈ D)
    (hinv : IsUnit (averagedPhaseHessian f w₀ q w)) (e : E) :
    externalDerivative f e q w =
      inner ℝ (transferCoefficient f w₀ e q w) (gradient (f q) w) := by
  have hslice : ContDiffOn ℝ ∞ (f q) D := by
    intro v hv
    exact ((hf.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, hv⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hzero := externalDerivative_at_critical_eq_zero
    ((hf.contDiffAt ((hU.prod hD).mem_nhds ⟨hq, h₀⟩)).differentiableAt (by simp))
    hw₀ hcritical hvalue e
  have hscalar := externalDerivative_sub_eq_inner_averagedExternalGradient hD hcD
    (contDiffOn_externalDerivative hU hD hf hq e) h₀ hw
  rw [hzero, sub_zero] at hscalar
  rw [transferCoefficient, ContinuousLinearMap.adjoint_inner_left,
    gradient_eq_averagedPhaseHessian hD hcD hslice h₀ hw hcritical,
    ← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hinv]
  exact hscalar

/-- The zeroth coefficient budget from the primitive mixed phase derivative
and the uniform inverse gap. No frequency factor occurs. This is the lowest
order of `new:eq:carrier-coefficient`, for the original direct-envelope bound. -/
theorem norm_transferCoefficient_le
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
    (e q : E) (w : CarrierVariables n) {B M : ℝ}
    (hB : ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (externalDerivative f e q) (w₀ q + t • (w - w₀ q))‖ ≤ M) :
    ‖transferCoefficient f w₀ e q w‖ ≤ B * M := by
  have hg : ‖averagedExternalGradient f w₀ e q w‖ ≤ M := by
    unfold averagedExternalGradient
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := M) (fun t ht ↦ (by
        simpa only [gradient, LinearIsometryEquiv.norm_map] using
          hM t ⟨(by simpa using ht.1 : 0 < t).le, by simpa using ht.2⟩))
  unfold transferCoefficient
  calc
    _ ≤ ‖(Ring.inverse (averagedPhaseHessian f w₀ q w)).adjoint‖ *
        ‖averagedExternalGradient f w₀ e q w‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ *
        ‖averagedExternalGradient f w₀ e q w‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ B * M := mul_le_mul hB hg (norm_nonneg _) ((norm_nonneg _).trans hB)

end JanetCartan.ResponseTransfer.DirectEvolution
