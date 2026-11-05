module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedInputMass
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassData
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

/-! A short numeric DATA name for the original selected unweighted Fourier mass.
This is the literal existing input, with no estimate assumed. The separate name
lets the full-forcing Picard application retain shared source DATA under ordinary
kernel limits (`main:eq:primary-fixed-scales`). -/
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedInputMassDataTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "name_original_selected_input_mass " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "original numeric mass: unknown publication mode"
  forallBoundedTelescope (← getConstInfo (root ++ `selected_fourierMass_le)).type (some 42) fun p old => do
    unless p.size == 42 do throwError "original numeric mass: selected42 changed"
    unless old.isAppOfArity (root ++ `fourierMass_statement) 55 do
      throwError "original numeric mass: selected theorem lost native55 statement"
    let native := old.getAppArgs
    let mass := app (root ++ `fourierMassValue) native
    let named := app (root ++ `selected_fourierMassValue) p
    let proof := if mode.getNat == 0 then mass else app (root ++ `fourierMassValue_le) native
    let target ← if mode.getNat == 0 then pure (mkConst ``Real) else do
      let literal ← inferType proof
      pure (literal.replace fun e => if e == mass then some named else none)
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "original numeric mass: unknown constants {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "original numeric mass: unresolved or additional input"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ (if mode.getNat == 0 then `selected_fourierMassValue else `selected_fourierMassValue_le)
    liftM <| IO.eprintln s!"original numeric mass: kernel checking {name}/42"
    if mode.getNat == 0 then
      addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
    else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The exact SAME original selected unweighted Fourier mass of (A i).adjoint(Q0(smoothResidualToL2 r)), with unchanged detector1. Original selected39/prefix/sourceDATA/index; no division by weight, new source or analytic success assumption (main:eq:primary-fixed-scales)."
    liftM <| IO.eprintln s!"original numeric mass: kernel passed {name}/42"
end JanetCartan.PhysicalMean.OriginalSelectedInputMassDataTemplate
end
name_original_selected_input_mass 0
name_original_selected_input_mass 1
