module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassData
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# The exact input mass DATA before the two unused numerical guards

The actual unweighted input is defined at native50/J/source/index (53 data).
The gamma and R90 admissions are used only in its bound, not in its value.
This names the literal frozen native55 body on that smallest existing data
boundary, also used by physical synthesis; no hypothesis is removed from any
estimate (`main:eq:primary-fixed-scales`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputMassValueTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "name_original_unguarded_input_mass_data " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "original native mass DATA53: unknown mode"
  let ci ← getConstInfo (root ++ `fourierMassValue)
  let some body := ci.value? (allowOpaque := true)
    | throwError "original native mass DATA53: native scalar unavailable"
  forallBoundedTelescope ci.type (some 55) fun p _ => do
    unless p.size == 55 do throwError "original native mass DATA53: original boundary changed"
    let raw := (body.beta p).headBeta
    unless !raw.containsFVar p[50]!.fvarId! && !raw.containsFVar p[51]!.fvarId! do
      throwError "original native mass DATA53: a numerical proof unexpectedly entered the literal input"
    let slim := p[:50].toArray ++ p[52:].toArray
    let named := app (root ++ `fourierMassValueData) slim
    let old := app (root ++ `fourierMassValue) p
    let proof := if mode.getNat == 0 then raw else app (root ++ `fourierMassValue_le) p
    let target ← if mode.getNat == 0 then pure (mkConst ``Real) else do
      let t ← inferType proof
      pure (t.replace fun e => if e == old then some named else none)
    let params := if mode.getNat == 0 then slim else p
    let type ← instantiateMVars (← mkForallFVars params target)
    let value ← instantiateMVars (← mkLambdaFVars params proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "original native mass DATA53: missing {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "original native mass DATA53: extra data or estimate field escaped"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ (if mode.getNat == 0 then `fourierMassValueData else `fourierMassValueData_le)
    liftM <| IO.eprintln s!"original native mass DATA53: kernel checking {name}/{params.size}"
    if mode.getNat == 0 then
      addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
    else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The literal original unweighted Fourier mass on its natural native50/J/source/index DATA53 boundary. Only the bound retains the original gamma/R90 guards, so no analytic premise is weakened; no inverse weight or changed physical input (main:eq:primary-fixed-scales)."
    liftM <| IO.eprintln s!"original native mass DATA53: kernel passed {name}/{params.size}"
end JanetCartan.PhysicalMean.OriginalCanonicalInputMassValueTemplate
end
name_original_unguarded_input_mass_data 0
name_original_unguarded_input_mass_data 1
