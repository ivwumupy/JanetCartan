module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMeanError
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanResidualCore
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-! Discharge BOTH original-core hypotheses in physical59 using the SAME already
selected OriginalFinalCore, not a changed physical cutoff. The only numeric
gates remain INITIAL Serror≤R0 and CURRENT 2m≤R (`main:prop:mean`).
Execution is staged until physical59 has its checked canonical export. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanCoreError
open Lean Meta Elab Command
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
run_elab do
  let fields := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
  let cores := `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore
  let old := fields ++ `physicalMean_error_le_picard_residual
  forallBoundedTelescope (← getConstInfo old).type (some 57) fun p _ => do
    unless p.size == 57 do throwError "actual fixed-core error: physical59 boundary changed"
    let gate ← inferType p[54]!
    unless gate.isAppOfArity ``LE.le 4 && gate.getAppArgs[2]!.isAppOfArity
        `JanetCartan.PhysicalMean.OriginalMeanErrorTransfer.Serror 44 do
      throwError "actual fixed-core error: changed original INITIAL Serror gate"
    let fixed := gate.getAppArgs[2]!.getAppArgs
    let C := app (cores ++ `core) fixed
    let subsets := app (cores ++ `core_subsets) fixed
    let x := p[56]!
    let membership ← Term.TermElabM.run'
      (PhysicalBackground.NativeReferenceSourceTemplate.termWith [(`x,x),(`C,C)] "x ∈ C")
    withLocalDeclNoLocalInstanceUpdate `hxOriginalFinalCore .default membership fun hx => do
      let hc := mkAppN (Expr.proj ``And 0 subsets) #[x,hx]
      let hp := mkAppN (Expr.proj ``And 1 subsets) #[x,hx]
      let proof := app old (p ++ #[hc,hp])
      let target ← inferType proof
      let params := p.push hx
      let type ← instantiateMVars (← mkForallFVars params target)
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
        unless missing.isEmpty do throwError "actual fixed-core error: missing {missing.toList}"
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
          throwError "actual fixed-core error: extra field or analytic success premise"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := fields ++ `physicalMean_error_on_common_core
      liftM <| IO.eprintln s!"actual fixed-core error: kernel checking {name}/58"
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "Actual unchanged-cutoff Schwartz mean error on the SAME existing OriginalFinalCore. Both physical/cancellation core memberships are proved from original44; only Serror initial reach and finite-moment current reach remain numerical. No new selector, profile, regularity or mean-success premise (main:prop:mean, main:eq:mean-equation)."
      liftM <| IO.eprintln s!"actual fixed-core error: kernel passed {name}/58"
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanCoreError
end
