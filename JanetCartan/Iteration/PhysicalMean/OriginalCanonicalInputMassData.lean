module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMass
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
/-!
# Native numeric name for the exact unweighted Fourier mass

Name the literal left side BEFORE substituting the original selected tuple.
The checked native55 statement and proof are unchanged. This small native alias
lets subsequent selected/full-source applications share the exact inverse input
without repeatedly expanding it (`main:eq:primary-fixed-scales`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputMassDataTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "name_original_native_input_mass " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "native numeric mass: unknown mode"
  let statement := root ++ `fourierMass_statement
  let ci ← getConstInfo statement
  let some body := ci.value? (allowOpaque := true)
    | throwError "native numeric mass: unavailable checked native statement"
  forallBoundedTelescope ci.type (some 55) fun p _ => do
    unless p.size == 55 do throwError "native numeric mass: native55 changed"
    let literal := (body.beta p).headBeta
    unless literal.isAppOfArity ``LE.le 4 do throwError "native numeric mass: expected original scalar inequality"
    let raw := literal.getAppArgs[2]!
    let named := app (root ++ `fourierMassValue) p
    let target := if mode.getNat == 0 then mkConst ``Real else
      literal.replace fun e => if e == raw then some named else none
    let proof := if mode.getNat == 0 then raw else app (root ++ `fourierMass_le) p
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "native numeric mass: missing {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "native numeric mass: unresolved or additional source/analytic input"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ (if mode.getNat == 0 then `fourierMassValue else `fourierMassValue_le)
    liftM <| IO.eprintln s!"native numeric mass: kernel checking {name}/55"
    if mode.getNat == 0 then
      addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
    else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "Literal original unweighted Fourier mass and its already proved Cmass44*H^(n+1) bound, named on native55 before selected substitutions. No inverse weight, new source or analytic hypothesis; the original gamma/R90 numeric guards are unchanged (main:eq:primary-fixed-scales)."
    liftM <| IO.eprintln s!"native numeric mass: kernel passed {name}/55"
end JanetCartan.PhysicalMean.OriginalCanonicalInputMassDataTemplate
end
name_original_native_input_mass 0
name_original_native_input_mass 1
