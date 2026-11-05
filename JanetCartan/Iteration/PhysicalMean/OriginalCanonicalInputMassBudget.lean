module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMoment
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Source-only cost for the exact unweighted original input

This is the numerical constant used by the actual mass consumer of the sole
sampled primitive tuple. It precedes R0, every history, sample, cutoff and source.
The SAME task100 global inverse profile and task89 original bare tester/adjoint
budgets are used; neither a source norm nor a mass estimate is a parameter
(`main:eq:primary-fixed-scales`, `app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputMassBudget
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def applyFields (name : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "static mass budget gained universe inputs"
  let mut type := info.type
  let mut value := mkConst name
  while type.isForall do
    let .forallE key _ body _ := type | throwError "static mass budget changed binder"
    let key := key.eraseMacroScopes
    let some (_,argument) := fields.find? (fun p => p.1 == key)
      | throwError "static mass budget missing original {key}"
    value := mkApp value argument
    type := body.instantiate1 argument
  return value

private def save (key : Name) (p : Array Expr) (value : Expr) (data : Bool)
    (expected : Option Expr := none) : MetaM Unit := do
  unless p.size == 44 do throwError "static mass budget must precede R0/history/sample/prefix/source"
  let type ← instantiateMVars (← mkForallFVars p (expected.getD (← inferType value)))
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "static mass budget missing producers {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "static mass budget has an extra input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact original unweighted Fourier-mass cost at q=n+1, using the same static44 primitive budgets and global inverse. No history, sample, prefix, source or mass-success input (main:eq:primary-fixed-scales)."

run_elab OriginalMeanQuadraticRealization.withActualQuadraticStaticPrimitives fun p original => do
  let inv := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
  let fields := original ++ #[(`Cinv,app (inv ++ `Cinv) p),(`hCinv,app (inv ++ `Cinv_nonneg) p)]
  let cost ← applyFields `JanetCartan.PhysicalMean.OriginalCanonicalInput.sourceMassConstant fields
  save `Cmass p cost true
  let proof ← applyFields `JanetCartan.PhysicalMean.OriginalCanonicalInput.sourceMassConstant_nonneg fields
  let target := (← inferType proof).replace fun e =>
    if e == cost then some (app (root ++ `Cmass) p) else none
  save `Cmass_nonneg p proof false (some target)
  logInfo "original unweighted mass cost44: actual primitive tester/adjoint + SAME global inverse, before history/sample/prefix/source"

end JanetCartan.PhysicalMean.OriginalCanonicalInputMassBudget
end
