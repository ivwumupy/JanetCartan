module

public import JanetCartan.Iteration.PhysicalMean.Completion
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionProfiles
public import JanetCartan.Iteration.PhysicalInitialization.SuppliedLeading
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual original geometric transfer of the completed mean error

The SAME original bare frame already has the required strain tolerance. Apply
its actual source-dilation frame proof on the wide original closed-b / ball-R
geometry, then choose the initial threshold before any history or tensor.
Consumer: the actual selected physical Picard residual and
`new:eq:mean-error-formula`, `main:prop:mean`.

The W/target/self fields are smooth DATA. Their actual producer, residual
precision and global Schwartz profiles are separate joins, not assumed mean
success. In particular this does not infer a physical cutoff-support profile
from the smaller background core.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanErrorTransfer
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
private def root := `JanetCartan.PhysicalMean.OriginalMeanErrorTransfer
private def app (name : Name) (p : Array Expr) : Expr := mkAppN (mkConst name) p
private def bodyAt (name : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "original error transfer: unavailable producer {name}"
  return (value.beta p).headBeta
private def tail (proof : Expr) (k : Nat) : Expr :=
  Nat.rec (motive := fun _ => Expr) proof (fun _ h => Expr.proj ``And 1 h) k
private def part (proof : Expr) (k : Nat) : Expr := Expr.proj ``And 0 (tail proof k)
private def termWith (values : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith values text)
private partial def dropLets (type : Expr) : Expr :=
  match type.consumeMData.headBeta with
  | .letE _ _ value body _ => dropLets (body.instantiate1 value)
  | other => other

private def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "original error transfer: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original error transfer: late or unproved input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original bare-frame/source-dilation geometric completed-mean error transfer: SAME native current, original wide b/R, initial Serror before R0/history/tensor data and dimension-only projected-stress reconstruction factor. No assumed current-frame or completed-mean estimate (new:eq:mean-error-formula)."
  logInfo m!"actual original error transfer {key}/{p.size}"

run_elab withActualInverse fun d => do
  withTransparency .default do
    let p := d.parameters
    let native := d.native39
    unless p.size == 50 && native.size == 39 do throwError "original error transfer: changed original50/39"
    let n := native[0]!
    let hn := native[1]!
    let eps := native[2]!
    unless eps.isAppOfArity ``Classical.choose 3 do
      throwError "original error transfer: changed SAME selected bare epsilon {eps.getAppFn.constName?}/{eps.getAppNumArgs}"
    unless eps.getAppArgs.back!.isAppOf `JanetCartan.PhysicalSampling.OriginalBare.exists_frame do
      throwError "original error transfer: epsilon was not the original bare frame choice"
    let frameSpec := mkAppN (mkConst ``Classical.choose_spec eps.getAppFn.constLevels!) eps.getAppArgs
    let strainCap := part frameSpec 3
    let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref native[:23].toArray
    let dilation ← bodyAt `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref native[:23].toArray
    unless dilation.isAppOfArity `JanetCartan.sourceDilationReference 5 do
      throwError "original error transfer: changed actual source-dilation reference"
    unless dilation.getAppArgs[2]! == native[21]! do
      throwError "original error transfer: another source dilation"
    let hframe ← withLocalDeclNoLocalInstanceUpdate `component .default (app ``Fin #[n]) fun i => do
      let raw := app `JanetCartan.PhysicalInitialization.supplied_original_source_frame
        (native[:18].toArray ++ #[native[21]!,Expr.proj ``And 0 native[22]!,dilation.getAppArgs[4]!,i])
      let proof ← mkAppM ``lt_of_lt_of_le #[raw,strainCap]
      mkLambdaFVars #[i] proof
    let H := app `JanetCartan.PhysicalSeed.ReferenceBoundary.H native[:18].toArray
    let same := app `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5 native[:18].toArray
    let geom (key : Name) := app (`JanetCartan.PhysicalSeed.OriginalBoundary ++ key) #[n,hn]
    let hR ← termWith [(`Gref,Gref),(`H,H),(`R,geom `R),(`same,same),(`hOriginal,geom `R_lt_chartRadius)]
      "(by change R < H.domain.chartRadius; rw [same]; exact hOriginal : R < Gref.domain.chartRadius)"
    let hStar ← termWith [(`n,n),(`rStar,native[26]!),(`h,native[28]!)]
      "(by change (2*(n+1)+14) ≤ rStar at h; omega : 8 ≤ rStar)"
    let producer := app `JanetCartan.PhysicalMean.exists_history_completedMean_error_transfer
      #[n,hn,Gref,geom `b,geom `R,geom `b_pos,geom `b_lt_R,hR,native[24]!,native[25]!,
        native[26]!,native[27]!,hStar,native[29]!,hframe]
    save `exists_error_transfer p[:44].toArray producer

private def choiceAt (name : Name) (type proof : Expr) : MetaM Expr := do
  unless type.isAppOfArity ``Exists 2 do throwError "original error transfer: missing original existential"
  return mkAppN (mkConst name type.getAppFn.constLevels!) (type.getAppArgs.push proof)

elab "select_original_mean_error_transfer " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "original error transfer: unknown selection mode"
  forallBoundedTelescope (← getConstInfo (root ++ `exists_error_transfer)).type (some 44) fun p type => do
    let proof := app (root ++ `exists_error_transfer) p
    let rawS ← choiceAt ``Classical.choose type proof
    if mode.getNat == 0 then
      save `Serror p rawS true
    else
      let S := app (root ++ `Serror) p
      let spec ← choiceAt ``Classical.choose_spec type proof
      let body := type.appArg!.beta #[rawS]
      unless body.isAppOfArity ``And 2 do throwError "original error transfer: changed threshold specification"
      let index := if mode.getNat == 1 then 0 else 1
      let expected := body.getAppArgs[index]!.replace fun e => if e == rawS then some S else none
      save (if mode.getNat == 1 then `two_le_Serror else `continuation) p
        (Expr.proj ``And index spec) false (some expected)

select_original_mean_error_transfer 0
select_original_mean_error_transfer 1
select_original_mean_error_transfer 2

run_elab withActualInverse fun d => do
  withTransparency .default do
    let p := d.parameters
    let S := app (root ++ `Serror) p[:44].toArray
    let gate ← mkAppM ``LE.le #[S,p[44]!]
    withLocalDeclNoLocalInstanceUpdate `hErrorReached .default gate fun hS => do
      let history := #[p[44]!,hS] ++ p[46:50].toArray
      let stem := app (root ++ `continuation) (p[:44].toArray ++ history)
      forallBoundedTelescope (← inferType stem) (some 6) fun tensors _ => do
        unless tensors.size == 6 do throwError "original error transfer: changed smooth W/target/self DATA"
        let proof := mkAppN stem tensors
        let rawType := dropLets (← inferType proof)
        let mapEq := app `JanetCartan.PhysicalMean.OriginalNormalCompletionProfiles.current_map_eq p
        let mapType ← inferType mapEq
        unless mapType.isAppOfArity ``Eq 3 do throwError "original error transfer: changed actual map identity"
        let actualF := mapType.getAppArgs[1]!
        let rawF := mapType.getAppArgs[2]!
        let target := rawType.replace fun e => if e == rawF then some actualF else none
        unless (target.find? (· == actualF)).isSome do
          throwError "original error transfer: actual native current was not retained"
        save `smooth_and_error (p ++ #[hS] ++ tensors) proof false (some target)

end JanetCartan.PhysicalMean.OriginalMeanErrorTransfer
end
