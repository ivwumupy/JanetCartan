module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Primitive

/-!
# Differentiating the actual critical equation

The implicit-map step in `paper-v2.tex`, `new:eq:carrier-coefficient`.
The inverse bound is that of the literal segment average, evaluated at its
critical endpoint. The critical-map derivative is a conclusion. Its consumer
is the moving-segment budget for `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- At the critical endpoint the literal segment average is exactly the
pointwise Hessian. Thus its gap also controls the implicit critical equation
(`new:eq:carrier-coefficient`). -/
theorem averagedPhaseHessian_at_critical
    (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n) (q : E) :
    averagedPhaseHessian f w₀ q (w₀ q) = fderiv ℝ (gradient (f q)) (w₀ q) := by
  simp [averagedPhaseHessian]

/-- Differentiating `∇w f(q,w₀(q)) = 0` solves for the actual first critical
jet using the same averaged-Hessian inverse. No derivative bound on `w₀`
is an input (`new:eq:carrier-coefficient`). -/
theorem fderiv_criticalPoint_eq
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (h₀ : w₀ q ∈ D) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : ∀ p ∈ U, gradient (f p) (w₀ p) = 0)
    (hinv : IsUnit (averagedPhaseHessian f w₀ q (w₀ q))) :
    fderiv ℝ w₀ q = -(Ring.inverse (averagedPhaseHessian f w₀ q (w₀ q))).comp
      ((fderiv ℝ (fun p : E × CarrierVariables n ↦ gradient (f p.1) p.2) (q, w₀ q)).comp
        (ContinuousLinearMap.inl ℝ E (CarrierVariables n))) := by
  let G : E × CarrierVariables n → CarrierVariables n := fun p ↦ gradient (f p.1) p.2
  let H := averagedPhaseHessian f w₀ q (w₀ q)
  let A := fderiv ℝ G (q, w₀ q)
  have hG := ((contDiffOn_jointPhaseGradient hU hD hf).contDiffAt (x := (q, w₀ q))
    ((hU.prod hD).mem_nhds ⟨hq, h₀⟩)).differentiableAt (by simp)
  have htotal := hG.hasFDerivAt.comp q ((hasFDerivAt_id q).prodMk hw₀.hasFDerivAt)
  have hzero : (fun p ↦ G (p, w₀ p)) =ᶠ[𝓝 q] (fun _ ↦ 0) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    exact hcritical p hp
  have htotalzero : ∀ e, A (e, fderiv ℝ w₀ q e) = 0 := by
    intro e
    have he := congrArg (fun T : E →L[ℝ] CarrierVariables n ↦ T e)
      (htotal.fderiv.symm.trans
        ((hasFDerivAt_const (𝕜 := ℝ) (0 : CarrierVariables n) q).congr_of_eventuallyEq hzero).fderiv)
    simpa [A] using he
  have hright : ∀ v, A (0, v) = H v := by
    intro v
    have he := congrArg (fun T : CarrierVariables n →L[ℝ] CarrierVariables n ↦ T v)
      (hG.hasFDerivAt.comp (w₀ q) (hasFDerivAt_prodMk_right (𝕜 := ℝ) q (w₀ q))).fderiv
    simpa [A, G, H, averagedPhaseHessian_at_critical, Function.comp_def] using he.symm
  ext e
  change fderiv ℝ w₀ q e = -((Ring.inverse H) (A (e, 0)))
  have hsplit : (e, fderiv ℝ w₀ q e) = (e, 0) + (0, fderiv ℝ w₀ q e) := by simp
  have hz := htotalzero e
  rw [hsplit, map_add, hright] at hz
  have heq : H (fderiv ℝ w₀ q e) = -A (e, 0) := eq_neg_of_add_eq_zero_right hz
  have he := congrArg (fun v : CarrierVariables n ↦ (Ring.inverse H) v) heq
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hinv] at he
  simpa using he

/-- The first critical jet is bounded by the primitive second joint phase
jet and the literal average's inverse gap. The bound is uniform in the
phase family and contains no frequency (`new:eq:carrier-coefficient`). -/
theorem norm_fderiv_criticalPoint_le_phase
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {q : E} (hq : q ∈ U) (h₀ : w₀ q ∈ D) (hw₀ : DifferentiableAt ℝ w₀ q)
    (hcritical : ∀ p ∈ U, gradient (f p) (w₀ p) = 0)
    (hinv : IsUnit (averagedPhaseHessian f w₀ q (w₀ q)))
    {B : ℝ} (hB : ‖Ring.inverse (averagedPhaseHessian f w₀ q (w₀ q))‖ ≤ B) :
    ‖fderiv ℝ w₀ q‖ ≤ B * ‖iteratedFDeriv ℝ 2 (Function.uncurry f) (q, w₀ q)‖ := by
  rw [fderiv_criticalPoint_eq hU hD hf hq h₀ hw₀ hcritical hinv, norm_neg]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul hB _ (norm_nonneg _) ((norm_nonneg _).trans hB)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousLinearMap.norm_inl_le_one ℝ E (CarrierVariables n))).trans
  simpa only [norm_iteratedFDeriv_one] using
    norm_jet_jointPhaseGradient_le_phase hU hD hf 1 ⟨hq, h₀⟩

end JanetCartan.ResponseTransfer.DirectEvolution
