module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Smooth

/-!
# Primitive phase budgets for the actual partial derivatives

The two primitive derivatives in `paper-v2.tex`, `new:eq:carrier-coefficient`,
cost exactly two joint phase orders. These norm comparisons do not assume
any partial-Hessian, critical-map or transferred-coefficient jet bound.
The consumer is the averaged-Hessian coefficient budget for the original
`paper.tex`, `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

private theorem norm_jet_fderiv_contraction_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : X → Y} {h : X → Z} {S : Set X}
    (hS : IsOpen S) (hg : ContDiffOn ℝ ∞ g S)
    (T : (X →L[ℝ] Y) →L[ℝ] Z) {C : ℝ} (hT : ‖T‖ ≤ C)
    (heq : EqOn h (T ∘ fderiv ℝ g) S) (j : ℕ) {x : X} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ j h x‖ ≤ C * ‖iteratedFDeriv ℝ (j + 1) g x‖ := by
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hx j
  rw [iteratedFDerivWithin_of_isOpen j hS hx,
    iteratedFDerivWithin_of_isOpen j hS hx] at he
  rw [he]
  have hd := (hg.contDiffAt (hS.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
  exact (T.norm_iteratedFDeriv_comp_left hd (by simp)).trans (by
    rw [norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_right hT (norm_nonneg _))

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual joint integration-variable gradient costs one primitive
phase derivative, with operator norm constant one
(`new:eq:carrier-coefficient`). -/
theorem norm_jet_jointPhaseGradient_le_phase
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (j : ℕ) {z : E × CarrierVariables n} (hz : z ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j (fun p : E × CarrierVariables n ↦ gradient (f p.1) p.2) z‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) (Function.uncurry f) z‖ := by
  let R : ((E × CarrierVariables n) →L[ℝ] ℝ) →L[ℝ] (CarrierVariables n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (CarrierVariables n) (E × CarrierVariables n) ℝ).flip
      (ContinuousLinearMap.inr ℝ E (CarrierVariables n))
  let T := (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp R
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖(InnerProductSpace.toDual ℝ (CarrierVariables n)).symm (R A)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map, one_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ E (CarrierVariables n)))
  apply (norm_jet_fderiv_contraction_le (hU.prod hD) hf T hT ?_ j hz).trans_eq
    (one_mul _)
  intro p hp
  have he := ((hf.contDiffAt ((hU.prod hD).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  exact congrArg (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm he.fderiv

/-- The actual joint `w`-Hessian costs two primitive joint phase derivatives.
This is the denominator integrand budget in `new:eq:carrier-coefficient`. -/
theorem norm_jet_jointPhaseHessian_le_phase
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (j : ℕ) {z : E × CarrierVariables n} (hz : z ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j
      (fun p : E × CarrierVariables n ↦ fderiv ℝ (gradient (f p.1)) p.2) z‖ ≤
      ‖iteratedFDeriv ℝ (j + 2) (Function.uncurry f) z‖ := by
  let G : E × CarrierVariables n → CarrierVariables n := fun p ↦ gradient (f p.1) p.2
  let T : ((E × CarrierVariables n) →L[ℝ] CarrierVariables n) →L[ℝ]
      (CarrierVariables n →L[ℝ] CarrierVariables n) :=
    (ContinuousLinearMap.compL ℝ (CarrierVariables n) (E × CarrierVariables n)
      (CarrierVariables n)).flip (ContinuousLinearMap.inr ℝ E (CarrierVariables n))
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [one_mul] using mul_le_of_le_one_right (norm_nonneg A)
        (ContinuousLinearMap.norm_inr_le_one ℝ E (CarrierVariables n)))
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ D) := contDiffOn_jointPhaseGradient hU hD hf
  have heq : EqOn (fun p : E × CarrierVariables n ↦ fderiv ℝ (gradient (f p.1)) p.2)
      (T ∘ fderiv ℝ G) (U ×ˢ D) := by
    intro p hp
    change fderiv ℝ (fun w ↦ G (p.1, w)) p.2 =
      (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E (CarrierVariables n))
    exact (((hG.contDiffAt ((hU.prod hD).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  have hb := norm_jet_fderiv_contraction_le (hU.prod hD) hG T hT
    (h := fun p : E × CarrierVariables n ↦ fderiv ℝ (gradient (f p.1)) p.2)
    heq j hz
  simp only [one_mul] at hb
  exact hb.trans (norm_jet_jointPhaseGradient_le_phase hU hD hf (j + 1) hz)

/-- External differentiation costs one phase order and the norm of the
external direction. All jets remain joint (`new:eq:carrier-coefficient`). -/
theorem norm_jet_jointExternalDerivative_le_phase
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (e : E) (j : ℕ) {z : E × CarrierVariables n} (hz : z ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j
      (fun p : E × CarrierVariables n ↦ externalDerivative f e p.1 p.2) z‖ ≤
      ‖e‖ * ‖iteratedFDeriv ℝ (j + 1) (Function.uncurry f) z‖ := by
  let T := ContinuousLinearMap.apply ℝ ℝ (e, (0 : CarrierVariables n))
  apply norm_jet_fderiv_contraction_le (hU.prod hD) hf T ?_ ?_ j hz
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e)
    intro A
    simpa [T, mul_comm] using A.le_opNorm (e, (0 : CarrierVariables n))
  · intro p hp
    have he := ((hf.contDiffAt ((hU.prod hD).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
    exact congrArg (fun A : E →L[ℝ] ℝ ↦ A e) he.fderiv

/-- The numerator integrand of the literal inverse-adjoint coefficient
costs exactly two joint phase orders, with no critical-map budget assumed
(`new:eq:carrier-coefficient`). -/
theorem norm_jet_jointExternalGradient_le_phase
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (e : E) (j : ℕ) {z : E × CarrierVariables n} (hz : z ∈ U ×ˢ D) :
    ‖iteratedFDeriv ℝ j
      (fun p : E × CarrierVariables n ↦ gradient (externalDerivative f e p.1) p.2) z‖ ≤
      ‖e‖ * ‖iteratedFDeriv ℝ (j + 2) (Function.uncurry f) z‖ :=
  (norm_jet_jointPhaseGradient_le_phase (f := externalDerivative f e) hU hD
    (contDiffOn_jointExternalDerivative hU hD hf e) j hz).trans
    (norm_jet_jointExternalDerivative_le_phase hU hD hf e (j + 1) hz)

end JanetCartan.ResponseTransfer.DirectEvolution
