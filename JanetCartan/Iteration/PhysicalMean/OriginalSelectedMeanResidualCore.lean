module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalCore
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# The already selected final defect core on the actual mean parameters

Reuse OriginalFinalCore's SAME original23 fixed minimum. Both inverse/physical
and cancellation cores contain it. The physical cutoff and its chart stay
unchanged; no new selector, approximation-dependent core or analytic premise
is introduced. Consumer: the two honest core memberships in actual physical59
and its finite-precision consequence (`main:thm:step`, `main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped Topology
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCoreTemplate
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore
private def base := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def finalCore := `JanetCartan.RevisedUniform.OriginalFinalCore
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some v := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual common mean core: unavailable original body {key}"
  return (v.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual common mean core: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual common mean core: history or source data escaped fixed44"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual common mean core: kernel checking {name}/44"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME already selected OriginalFinalCore on the original23 tuple recovered from110 physical Dsmooth44. Both physical and cancellation cores contain this fixed compact neighborhood; no physical cutoff or chart is changed and no source/history/accuracy datum enters (main:thm:step, main:prop:mean)."
  liftM <| IO.eprintln s!"actual common mean core: kernel passed {name}/44"
elab "publish_original_selected_mean_residual_core " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "actual common mean core: unknown mode"
  withActualInverse fun d => withTransparency .default do
    let fixed := d.parameters[:44].toArray
    let n := d.native39[0]!
    let D := app (base ++ `Dsmooth) fixed
    let rawD ← bodyAt (base ++ `Dsmooth) fixed
    unless rawD.isAppOfArity `JanetCartan.RevisedUniform.OriginalSmoothing.Dsmooth 23 do
      throwError "actual common mean core: lost SAME original physical domain23"
    let ref := rawD.getAppArgs
    let rawCore := app (finalCore ++ `D) ref
    let C := app (root ++ `core) fixed
    if mode.getNat == 0 then
      save `core fixed rawCore (← inferType rawCore) true
    else if mode.getNat == 1 then
      let oldCancellation := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core d.native39[:21].toArray
      let physical ← termWith [(`D,D),(`n,n)] "D.core n"
      let h1 := app (finalCore ++ `subset_background_core) ref
      let h2 := app (finalCore ++ `subset_inverse_core) ref
      let a ← termWith [(`C,C),(`B,oldCancellation)] "C ⊆ B"
      let b ← termWith [(`C,C),(`P,physical)] "C ⊆ P"
      let proof := app ``And.intro #[a,b,h1,h2]
      save `core_subsets fixed proof (app ``And #[a,b])
    else
      let hc := app (finalCore ++ `isCompact) ref
      let hz := app (finalCore ++ `zero_mem_interior) ref
      let a ← termWith [(`C,C)] "IsCompact C"
      let b ← termWith [(`C,C),(`n,n)] "(0 : JanetCartan.Euclidean n) ∈ interior C"
      let proof := app ``And.intro #[a,b,hc,hz]
      save `compact_neighborhood fixed proof (app ``And #[a,b])
end JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCoreTemplate
end
publish_original_selected_mean_residual_core 0
publish_original_selected_mean_residual_core 1
publish_original_selected_mean_residual_core 2
