module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceIteration
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrent
public meta import Lean

/-! The actual final raw/native/wide inputs use the SAME finite source run,
component adjoint, global inverse, original shift and fixed prefix. No sample
weight or Fourier scalar is added to the unweighted physical datum. -/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputApplication
open Lean Meta Elab Command OriginalCanonicalSampledApplication

private def save (short : Name) (params : Array Expr) (term : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual final source input: missing constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual final source input: extra/unresolved actor or source input"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource ++ short
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  addDocStringCore name "The literal unweighted original input of the actual finite source: SAME A adjoint, global Q0, sample, shift and fixed prefix. sqrt μ belongs only to external synthesis, with no weight division or extra Fourier scalar (app:ch_mean_pairs:defn:mean-canonical; main:eq:primary-fixed-scales)."
  logInfo m!"actual final source {short}: native{params.size}, SAME unweighted component input"

elab "construct_actual_canonical_input " mode:num : command => liftTermElabM do
  withActualSample fun xs ξ _ _ _ => do
    withLocalDeclNoLocalInstanceUpdate `L .default (mkConst ``Nat) fun L => do
      withLocalDeclNoLocalInstanceUpdate `steps .default (mkConst ``Nat) fun steps => do
        let root := `JanetCartan.PhysicalMean.OriginalCanonicalSource
        let trial := xs ++ #[ξ,L]
        let params := trial.push steps
        if mode.getNat == 3 then
          let chosen := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
          let value := mkAppN (mkConst (root ++ `finalWideInput)) (xs ++ #[chosen,L,steps])
          save `selectedFinalWideInput (xs ++ #[L,steps]) value
          return
        let A := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalRow.A) trial
        let Q0 := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0) xs
        let source := mkAppN (mkConst (root ++ `iterate)) params
        let gen := `JanetCartan.PhysicalMean.OriginalCanonicalInput
        match mode.getNat with
        | 0 => save `finalRawInput params (← mkAppM (gen ++ `rawInput) #[A,Q0,source])
        | 1 => save `finalNativeInput params (← mkAppM (gen ++ `nativeInput) #[A,Q0,source])
        | 2 => save `finalWideInput params (← mkAppM (gen ++ `wideInput) #[A,Q0,L,source])
        | _ => throwError "actual final source input: unknown field"

end JanetCartan.PhysicalMean.OriginalCanonicalInputApplication
end
