module

public meta import Lean

/-!
# Finite scalar budgets on the identical original family

Sum only the already-proved per-row numerical constants. These sums precede
histories and frequencies; they do not change the rows, weights, kernels or
source. They supply the common sharp and summed-mean constants of
`exists_threshold_original_common_scalar_native_of_amplitude`
(`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalScalarFamilyApplication
open Lean Meta Elab Command

private def source : Name := `JanetCartan.PhysicalSampling.OriginalScalarHistory.Row
private def target : Name := `JanetCartan.PhysicalSampling.OriginalScalarFamily

private def store (name : Name) (params : Array Expr) (value : Expr)
    (expected : Option Expr := none) : MetaM Expr := do
  let rawType ← match expected with
    | some type => pure type
    | none => inferType value
  let type ← instantiateMVars rawType
  let value ← instantiateMVars value
  let type ← mkForallFVars params type
  let value ← mkLambdaFVars params value
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry ||
      type.hasFVar || value.hasFVar then
    throwError "actual scalar family: open or recovered declaration {name}"
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  else
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  logInfo m!"checked actual scalar finite-family budget {name}"
  return mkAppN (mkConst name) params

/-- Aggregate a single already-retained numeric bound without any new choice. -/
elab "cache_original_scalar_family_bound " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let names : Array Name := #[`Csharp, `Cmean]
  let positiveNames : Array Name := #[`hCsharp, `hCmean]
  let boundNames : Array Name := #[`Csharp_le, `Cmean_le]
  unless index < names.size do throwError "actual scalar family: invalid bound index"
  let bound := source ++ names[index]!
  forallBoundedTelescope (← getConstInfo bound).type (some 36) fun params tail => do
    unless params.size == 36 do throwError "actual scalar family: expected original36 prehistory parameters"
    let tail ← whnf tail
    unless tail.isForall do throwError "actual scalar family: missing SAME original row index"
    let rowType := tail.bindingDomain!
    let values := mkAppN (mkConst bound) params
    let positives := mkAppN (mkConst (source ++ positiveNames[index]!)) params
    let univ ← mkAppOptM `Finset.univ #[some rowType, none]
    let total ← store (target ++ names[index]!) params (← mkAppM `Finset.sum #[univ, values])
    let nonnegative ← withLocalDeclD `i rowType fun i => do
      let membership ← mkAppM `Finset.mem_univ #[i]
      withLocalDeclD `hi (← inferType membership) fun hi => do
        mkLambdaFVars #[i, hi] (← mkAppM `le_of_lt #[mkApp positives i])
    let htotal ← mkAppM `Finset.sum_nonneg #[nonnegative]
    let totalType ← inferType htotal
    let zero := totalType.appFn!.appArg!
    discard <| store (target ++ positiveNames[index]!) params htotal
      (some (← mkAppM ``LE.le #[zero, total]))
    withLocalDeclD `i rowType fun i => do
      let hi ← mkAppM `Finset.mem_univ #[i]
      let hbound ← mkAppM `Finset.single_le_sum #[nonnegative, hi]
      discard <| store (target ++ boundNames[index]!) (params.push i) hbound
        (some (← mkAppM ``LE.le #[mkApp values i, total]))

end JanetCartan.PhysicalSampling.OriginalScalarFamilyApplication
