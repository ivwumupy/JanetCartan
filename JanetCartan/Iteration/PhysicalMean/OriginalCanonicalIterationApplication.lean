module

public import JanetCartan.Iteration.PhysicalMean.Source
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampled
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public meta import Lean

/-!
# The actual finite fixed-source run

The linear and quadratic operators, source inverse, sample and prefix are fixed
before `steps`. The forcing is99's exact weighted background quadrature source
on the SAME original U. Trial data retain arbitrary shifts; the selected run
reuses the one named original shift, not a second event
(`app:ch_mean_pairs:eq:single-iteration`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalIterationApplication
open Lean Meta Elab Command
open OriginalCanonicalSampledApplication

private def save (short : Name) (params : Array Expr) (term : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual fixed source run: missing constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual fixed source run: extra/unresolved source input"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource ++ short
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  addDocStringCore name "The actual finite Picard source with the SAME fixed linear/quadratic actions and original background forcing. No successful source, new inverse, shift, prefix or profile is assumed (app:ch_mean_pairs:eq:single-iteration)."
  logInfo m!"actual fixed source {short}: native{params.size}, fixed operators/source before step count"

elab "construct_actual_canonical_iteration " mode:num : command => liftTermElabM do
  withActualSample fun xs ξ _ _ _ => do
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      withLocalDeclNoLocalInstanceUpdate `steps .default (mkConst ``Nat) fun steps => do
        let root := `JanetCartan.PhysicalMean.OriginalCanonicalSource
        match mode.getNat with
        | 0 =>
          let params := (xs.push ξ).push L
          let linear := mkAppN (mkConst (root ++ `linear)) params
          let quadratic := mkAppN (mkConst (root ++ `quadratic)) params
          let forcing := mkAppN (mkConst
            `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing) (xs.push ξ)
          let value ← mkAppM `JanetCartan.PhysicalMean.sourceIterate #[linear,quadratic,forcing,steps]
          save `iterate (params.push steps) value
        | 1 =>
          let chosen := mkAppN (mkConst
            `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
          let value := mkAppN (mkConst (root ++ `iterate)) (xs ++ #[chosen,L,steps])
          save `selected_iterate (xs ++ #[L,steps]) value
        | _ => throwError "actual fixed source run: unknown field"

end JanetCartan.PhysicalMean.OriginalCanonicalIterationApplication
end
