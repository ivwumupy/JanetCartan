module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualCosts
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Thresholds
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.AbstractAssembly
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# The actual constants in the final uniform-correction deduction

Instantiate the checked abstract assembly with the released original `C`,
`C_nonneg`, `T` and `T_reaches`. The sole remaining premise is the exact
same-history step21 theorem, with the existing reference, core, target and
initial threshold. The unconditional root must supply the actual step.

This thin application reuses the complete checked gate/coordinate assembly;
it introduces no new analytic input or successful-construction record
(`main:thm:step`, `main:prop:current-scale`, `main:thm:main`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionActualStaticTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def steps := `JanetCartan.RevisedUniform.OriginalStepEstimates
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def checked (name : Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual-static assembly: unfinished producer {name}: {axioms}"

run_meta do
  let deduction := root ++ `uniformCorrection_of_contracts
  checked deduction
  for key in #[`C,`C_nonneg,`T,`T_reaches] do checked (steps ++ key)
  forallBoundedTelescope (← getConstInfo (steps ++ `C)).type (some 7) fun fixed _ => do
    unless fixed.size == 7 do throwError "actual-static assembly: original metric7 changed"
    let proof := app deduction (fixed ++ #[app (steps ++ `C) fixed,
      app (steps ++ `C_nonneg) fixed,app (steps ++ `T) fixed,app (steps ++ `T_reaches) fixed])
    let remaining ← inferType proof
    unless remaining.isForall do
      throwError "actual-static assembly: exact step21 premise disappeared"
    forallBoundedTelescope remaining.bindingDomain! (some 14) fun p outcome => do
      unless p.size == 14 && outcome.isAppOfArity ``Exists 2 do
        throwError "actual-static assembly: extra premise or changed original step21"
    let type ← instantiateMVars (← mkForallFVars fixed remaining)
    let value ← instantiateMVars (← mkLambdaFVars fixed proof)
    let env ← getEnv
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "actual-static assembly: unresolved or additional input"
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do
        throwError "actual-static assembly: unavailable original metadata {missing.toList}"
    let name := root ++ `uniformCorrection_of_step
    if (env.find? name).isSome then throwError "actual-static assembly: duplicate {name}"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    IO.println "Kernel checking actual-static uniform assembly uniformCorrection_of_step/8"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The real original C(k), nonnegativity, T(k), current numerical reaches, Tpair(d,hn,1), reference/core and metric family are instantiated in the checked abstract assembly. The sole explicit premise is the exact original step21 producer; the unconditional root supplies that actual theorem. No new data or analytic hypothesis is introduced (main:thm:step; main:prop:current-scale; main:thm:main)."
    checked name
    logInfo m!"PASS actual-static uniform assembly uniformCorrection_of_step/8: {← collectAxioms name}"

end JanetCartan.RevisedUniform.OriginalUniformCorrectionActualStaticTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.uniformCorrection_of_step
