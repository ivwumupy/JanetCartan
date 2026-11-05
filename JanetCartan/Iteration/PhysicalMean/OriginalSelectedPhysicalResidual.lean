module

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedCoreResidual
public import JanetCartan.Iteration.PhysicalMean.Completion
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCompletedResidual
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The actual full Picard residual is the normalized physical reduced residual

Consumer: `exists_history_completedMean_error_transfer` and `new:eq:qT-identity`.
The selected target is replaced by its literal original finite-moment normalized
physical tensor on the unchanged core. The initialized field and full sampled
self tensor remain exactly those of the same selected E/Q and Picard run.
This is an identity, not a source estimate or a completed-mean estimate.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped Matrix.Norms.Frobenius

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual

private theorem pairing_of_completed_residual {n : ℕ} (P T B H : MetricTensor n)
    (r t : ℝ) (hr : r = t - tensorPairing P (B + H))
    (ht : t = tensorPairing P T) : r = tensorPairing P (T - B - H) := by
  rw [hr, ht]
  simp only [tensorPairing, Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private theorem vector_eq_of_components {n : ℕ} (v w : Euclidean n)
    (h : ∀ i, v i = w i) : v = w := by
  ext i
  exact h i

end JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args
private def bodyAt (name : Name) (args : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "physical residual: unavailable original producer {name}"
  return (value.beta args).headBeta
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)

run_elab do
  let original := `JanetCartan.PhysicalMean.OriginalSelectedCoreResidual.picard_residual_eq_projected_core_defect
  let completed := `JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual.residual_eq_projected_core_defect
  let some completedValue := (← getConstInfo completed).value? (allowOpaque := true)
    | throwError "physical residual: unavailable checked core proof"
  let helpers := completedValue.getUsedConstants.toList.filter
    (fun name => name.toString.endsWith ".leading_component_on_core")
  let [componentHelper] := helpers
    | throwError "physical residual: changed original measured-component helper"
  forallBoundedTelescope (← getConstInfo original).type (some 57) fun p _ => do
    unless p.size == 57 do throwError "physical residual: changed selected Picard/core57"
    let selected := p[:52].toArray
    let oldProof := app original p
    let oldType ← inferType oldProof
    unless oldType.isAppOfArity ``Eq 3 do throwError "physical residual: not the actual core equality"
    let rhs := oldType.getAppArgs[2]!
    unless rhs.isAppOfArity ``HSub.hSub 6 do throwError "physical residual: lost actual target minus self/strain"
    let targetComponent := rhs.getAppArgs[4]!
    let pair := rhs.getAppArgs[5]!
    unless pair.isAppOfArity `JanetCartan.tensorPairing 3 do throwError "physical residual: lost original projection"
    let P := pair.getAppArgs[1]!
    let combined := pair.getAppArgs[2]!
    unless combined.isAppOfArity ``HAdd.hAdd 6 do throwError "physical residual: lost full initialized strain plus self"
    let strain := combined.getAppArgs[4]!
    let selfAt := combined.getAppArgs[5]!
    unless strain.isAppOfArity `JanetCartan.linearizedMetric 5 do
      throwError "physical residual: changed full initialized strain {strain.getAppFn.constName?}/{strain.getAppNumArgs}"
    let n := strain.getAppArgs[0]!
    let N := strain.getAppArgs[1]!
    let F := strain.getAppArgs[2]!
    let W := strain.getAppArgs[3]!
    let x := p[54]!
    let hx := p[55]!
    let i := p[56]!
    unless strain.getAppArgs[4]! == x do throwError "physical residual: changed original point"
    if selfAt.containsFVar hx.fvarId! || selfAt.containsFVar i.fvarId! then
      throwError "physical residual: sampled self depends on a component or core-membership proof"
    let full ← bodyAt (forcing ++ `selectedFullSource) selected
    unless full.isAppOfArity (forcing ++ `completeSource) 4 do throwError "physical residual: changed full selected source"
    let native := full.getAppArgs[1]!.getAppArgs
    unless native.size == 50 do throwError "physical residual: lost literal native50"
    let meanEq ← inferType (app (forcing ++ `physicalAffineMean_eq_original) native)
    let originalMean := meanEq.getAppArgs[2]!
    unless originalMean.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.physicalMean 39 do
      throwError "physical residual: changed original affine mean39"
    let native39 := originalMean.getAppArgs
    let cancellation ← bodyAt `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native39
    unless cancellation.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
      throwError "physical residual: changed original retained cancellation64"
    let c := cancellation.getAppArgs
    let target := app (forcing ++ `selectedMeasuredTarget) selected
    let z := app `JanetCartan.torusQuotient #[n,x]
    let value := mkApp (app (forcing ++ `selected_target_value) selected) z
    let some periodized := (← inferType value).find?
        (·.isAppOfArity `JanetCartan.DefectSmoothing.tensorPeriodization 3)
      | throwError "physical residual: missing literal normalized tensor periodization"
    let tensor := periodized.getAppArgs[1]!
    unless tensor.isAppOf `JanetCartan.PhysicalSmoothing.normalizedSource && periodized.getAppArgs[2]! == z do
      throwError "physical residual: replaced the actual normalized target or original point"
    let hooks := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core_plateau native39[:21].toArray
    let hxMeasured := Expr.proj ``And 0 (mkAppN hooks #[x,hx])
    let ht := app componentHelper #[n,N,c[21]!,c[22]!,c[23]!,F,target,tensor,x,hxMeasured,value,i]
    let component := app ``pairing_of_completed_residual
      #[n,P,mkApp tensor x,strain,selfAt,oldType.getAppArgs[1]!,targetComponent,oldProof,ht]
    let selfField ← mkLambdaFVars #[x] selfAt
    let residual := app (source ++ `selected_residualWithForcing)
      (native ++ #[p[52]!,app (forcing ++ `selectedFullSource) selected,p[53]!])
    let lhs ← termWith [(`e,residual),(`z,z)] "e.val z ()"
    let rhs ← termWith [(`F,F),(`W,W),(`T,tensor),(`H,selfField),(`x,x)]
      "JanetCartan.PhysicalMean.reducedPhysicalResidual F W T H x"
    let proof := app ``vector_eq_of_components #[n,lhs,rhs,← mkLambdaFVars #[i] component]
    let params := p[:56].toArray
    let type ← instantiateMVars (← mkForallFVars params (← mkEq lhs rhs))
    let proof ← instantiateMVars (← mkLambdaFVars params proof)
    let env ← getEnv
    for e in #[type,proof] do
      let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
      unless missing.isEmpty do throwError "physical residual: missing original producers {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "physical residual: extra or unresolved input"
    let (type,proof) := Lean.ShareCommon.shareCommon (type,proof)
    let name := root ++ `picard_residual_eq_reduced_physical_residual
    addDecl (.thmDecl {name,levelParams := [],type,value := proof}) (forceExpose := true)
    addDocStringCore name "The SAME selected full-source Picard residual vector equals reducedPhysicalResidual of the original initialized field, literal normalizedSource target and full sampled self tensor on the unchanged original core. Only original data and point/core arguments; no source estimate, replacement target or unmeasured affine cancellation (new:eq:qT-identity)."
    logInfo "actual normalized physical residual56: SAME full-source Picard, initialized field, normalized target, full sampled self and original core"

end JanetCartan.PhysicalMean.OriginalSelectedPhysicalResidual
end
