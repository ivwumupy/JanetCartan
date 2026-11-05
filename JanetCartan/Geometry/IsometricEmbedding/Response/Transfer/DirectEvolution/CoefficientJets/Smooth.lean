module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic
public import JanetCartan.Analysis.Matrix.InverseBounds.Algebra
public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral

/-!
# Joint smoothness of the literal stationary transfer coefficient

The coefficient of `paper-v2.tex`, `new:eq:carrier-coefficient`, used by the
original `paper.tex`, `app:ch_response:eq:direct-envelope-profile`. All
variables remain in the same open product, and convexity keeps the entire
moving segment there. The critical map is assumed smooth, but no bound on
its derivatives or on the transferred coefficient is an input here.

The actual producers of the phase, critical map and inverse gap are the
compatible primary phase and the small-time two-time Hamilton geometry.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiffOn_secondPartial
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : X × Y → Z} {U : Set X} {D : Set Y}
    (hU : IsOpen U) (hD : IsOpen D) (hg : ContDiffOn ℝ ∞ g (U ×ˢ D)) :
    ContDiffOn ℝ ∞ (fun z : X × Y ↦ fderiv ℝ (fun w ↦ g (z.1, w)) z.2)
      (U ×ˢ D) := by
  intro z hz
  have h := (hg.contDiffAt ((hU.prod hD).mem_nhds hz)).comp (z, z.2)
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (h.fderiv contDiffAt_snd (m := ∞) (by simp)).contDiffWithinAt

/-- Joint smoothness of the actual integration-variable gradient, the
implicit equation used in `new:eq:carrier-coefficient`. -/
theorem contDiffOn_jointPhaseGradient
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D)) :
    ContDiffOn ℝ ∞ (fun z : E × CarrierVariables n ↦ gradient (f z.1) z.2)
      (U ×ˢ D) :=
  (InnerProductSpace.toDual ℝ (CarrierVariables n)).symm.contDiff.comp_contDiffOn
    (contDiffOn_secondPartial hU hD hf)

/-- Joint smoothness of the literal `w`-Hessian in the segment average
(`new:eq:carrier-coefficient`). -/
theorem contDiffOn_jointPhaseHessian
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D)) :
    ContDiffOn ℝ ∞
      (fun z : E × CarrierVariables n ↦ fderiv ℝ (gradient (f z.1)) z.2)
      (U ×ˢ D) :=
  contDiffOn_secondPartial hU hD (contDiffOn_jointPhaseGradient hU hD hf)

/-- Joint output/parameter and integration-variable smoothness of the
external derivative, keeping its direction fixed (`new:eq:carrier-ibp`). -/
theorem contDiffOn_jointExternalDerivative
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D)) (e : E) :
    ContDiffOn ℝ ∞ (fun z : E × CarrierVariables n ↦ externalDerivative f e z.1 z.2)
      (U ×ˢ D) := by
  intro z hz
  have h := (hf.contDiffAt ((hU.prod hD).mem_nhds hz)).comp (z, z.1)
    (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact ((h.fderiv contDiffAt_fst (m := ∞) (by simp)).clm_apply
    contDiffAt_const).contDiffWithinAt

/-- Joint smoothness of the mixed derivative in the numerator of the actual
inverse-adjoint coefficient (`new:eq:carrier-coefficient`). -/
theorem contDiffOn_jointExternalGradient
    {f : E → CarrierVariables n → ℝ} {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D)) (e : E) :
    ContDiffOn ℝ ∞
      (fun z : E × CarrierVariables n ↦ gradient (externalDerivative f e z.1) z.2)
      (U ×ˢ D) :=
  contDiffOn_jointPhaseGradient hU hD (contDiffOn_jointExternalDerivative hU hD hf e)

/-- The actual moving segment remains jointly smooth in its integration
parameter and all external variables (`new:eq:carrier-coefficient`). This
lemma is also the smoothness input for differentiating its finite jets. -/
theorem contDiffAt_criticalSegmentIntegrand
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : E × CarrierVariables n → F} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ D)) (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (h₀ : MapsTo w₀ U D) {z : ℝ × (E × CarrierVariables n)}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ (U ×ˢ D)) :
    ContDiffAt ℝ ∞ (fun y : ℝ × (E × CarrierVariables n) ↦
      H (y.2.1, w₀ y.2.1 + y.1 • (y.2.2 - w₀ y.2.1))) z := by
  have hmem : (z.2.1, w₀ z.2.1 + z.1 • (z.2.2 - w₀ z.2.1)) ∈ U ×ˢ D :=
    ⟨hz.2.1, hcD.add_smul_sub_mem (h₀ hz.2.1) hz.2.2 hz.1⟩
  have hw := (hw₀.contDiffAt (hU.mem_nhds hz.2.1)).comp z contDiffAt_snd.fst
  exact (hH.contDiffAt ((hU.prod hD).mem_nhds hmem)).comp z
    (contDiffAt_snd.fst.prodMk (hw.add (contDiffAt_fst.smul (contDiffAt_snd.snd.sub hw))))

variable [FiniteDimensional ℝ E]

/-- Smoothness of the literal averaged Hessian follows from the primitive
phase and moving-segment smoothness (`new:eq:carrier-coefficient`). -/
theorem contDiffOn_averagedPhaseHessian
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D) :
    ContDiffOn ℝ ∞ (Function.uncurry (averagedPhaseHessian f w₀)) (U ×ˢ D) := by
  apply contDiffOn_fixedIntervalIntegral (a := 0) (b := 1)
    (F := fun z : ℝ × (E × CarrierVariables n) ↦
      fderiv ℝ (gradient (f z.2.1)) (w₀ z.2.1 + z.1 • (z.2.2 - w₀ z.2.1)))
    (hU.prod hD)
  intro z hz
  exact contDiffAt_criticalSegmentIntegrand hU hD hcD
    (contDiffOn_jointPhaseHessian hU hD hf) hw₀ h₀ (by simpa using hz)

/-- Smoothness of the actual averaged external gradient, with all output
and parameter variables retained (`new:eq:carrier-coefficient`). -/
theorem contDiffOn_averagedExternalGradient
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D) (e : E) :
    ContDiffOn ℝ ∞ (Function.uncurry (averagedExternalGradient f w₀ e)) (U ×ˢ D) := by
  apply contDiffOn_fixedIntervalIntegral (a := 0) (b := 1)
    (F := fun z : ℝ × (E × CarrierVariables n) ↦
      gradient (externalDerivative f e z.2.1)
        (w₀ z.2.1 + z.1 • (z.2.2 - w₀ z.2.1))) (hU.prod hD)
  intro z hz
  exact contDiffAt_criticalSegmentIntegrand hU hD hcD
    (contDiffOn_jointExternalGradient hU hD hf e) hw₀ h₀ (by simpa using hz)

/-- Joint smoothness of the actual inverse-adjoint transfer coefficient.
The only inverse hypothesis concerns the same literal average on the same
product box (`new:eq:carrier-coefficient`). -/
theorem contDiffOn_transferCoefficient
    {f : E → CarrierVariables n → ℝ} {w₀ : E → CarrierVariables n}
    {U : Set E} {D : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (hw₀ : ContDiffOn ℝ ∞ w₀ U) (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) (e : E) :
    ContDiffOn ℝ ∞ (Function.uncurry (transferCoefficient f w₀ e)) (U ×ˢ D) := by
  have hH := contDiffOn_averagedPhaseHessian hU hD hcD hf hw₀ h₀
  have hG := contDiffOn_averagedExternalGradient hU hD hcD hf hw₀ h₀ e
  intro z hz
  have hi := (contDiffOn_ringInverse_units (N := ∞)).contDiffAt
    (Units.isOpen.mem_nhds (hinv z.1 hz.1 z.2 hz.2))
  exact (((ContinuousLinearMap.adjoint :
      (CarrierVariables n →L[ℝ] CarrierVariables n) ≃ₗᵢ[ℝ]
        (CarrierVariables n →L[ℝ] CarrierVariables n)).contDiff.contDiffAt.comp z
      (hi.comp z (hH.contDiffAt ((hU.prod hD).mem_nhds hz)))).clm_apply
      (hG.contDiffAt ((hU.prod hD).mem_nhds hz))).contDiffWithinAt

end JanetCartan.ResponseTransfer.DirectEvolution
