module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public meta import Lean

/-! # The same primary and normalized-history current

Read the current from the exact primary strain statement and the finite map
from its original normalized source. The consuming declaration is the actual
primary input of `OriginalStepEstimates` (`main:eq:primary-strain`,
`main:thm:step`). No source estimate or later accuracy is an input to this
identity. The statement and proof are checked in separate leaves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepFields.PrimaryCurrentTemplate

open Lean Meta Elab Command

def root : Name := `JanetCartan.RevisedUniform.OriginalStepFields
def statementName : Name := root ++ `primary_current_eq_normalized_history_statement
def proofName : Name := root ++ `primary_current_eq_normalized_history

private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args

private def rawForall (count : Nat) (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "primary current identity: original parameter boundary changed"
      withLocalDeclNoLocalInstanceUpdate name bi (domain.instantiateRev p) fun x =>
        loop k body (p.push x)

structure Currents where
  selected : Array Expr
  primary : Expr
  normalized : Expr
  functionType : Expr

/-- Read the two exact currents and reject any dependence on the six later
strain inputs or the point/core query. -/
def withCurrents (next : Currents → MetaM Unit) : MetaM Unit := do
  let strain := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.strain_statement
  let ci ← getConstInfo strain
  let some value := ci.value? (allowOpaque := true) |
    throwError "primary current identity: the checked strain statement is unavailable"
  rawForall 58 ci.type fun p _ => do
    let body := (value.beta p).headBeta
    rawForall 2 body fun _ inequality => do
      unless inequality.isAppOfArity ``LE.le 4 do
        throwError "primary current identity: the original pointwise inequality changed"
      let some linear := inequality.getAppArgs[2]!.find?
          (·.isAppOfArity `JanetCartan.linearizedMetric 4) |
        throwError "primary current identity: the original linearized metric disappeared"
      let primary := linear.getAppArgs[2]!
      let selected := p[:52].toArray
      let normal := `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget
      let ni ← getConstInfo normal
      let some nv := ni.value? (allowOpaque := true) |
        throwError "primary current identity: the original normalized source is unavailable"
      let source := (nv.beta selected).headBeta
      unless source.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
        throwError "primary current identity: normalizedSource10 changed"
      let a := source.getAppArgs
      let normalized := app `JanetCartan.RevisedGlobal.finiteMap
        #[a[0]!,a[1]!,a[2]!,a[8]!,a[9]!]
      unless primary.isAppOfArity `JanetCartan.RevisedGlobal.finiteMap 5 do
        throwError "primary current identity: the primary current is not its original finiteMap"
      for e in #[primary,normalized] do
        let closed ← mkLambdaFVars selected e
        if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars || closed.hasSorry then
          throwError "primary current identity: a point, gate, accuracy or amplitude escaped"
      next {selected,primary,normalized,functionType := ← inferType primary}

private def save (name : Name) (p : Array Expr) (value target : Expr)
    (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "primary current identity: unresolved expression in {name}"
    let missing := e.getUsedConstants.filter (fun key => (env.find? key).isNone)
    unless missing.isEmpty do
      throwError "primary current identity: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name
    "The exact current of the original primary strain statement equals the finiteMap of the SAME normalizedSource10, at selected52 before hAux/hOp/N/accuracy/amplitude. The step's actual primary input consumes this identity; no analytic premise is added (main:eq:primary-strain; main:thm:step)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "primary current identity: nonstandard axioms {axioms}"
  logInfo m!"PASS exact primary/normalized current {name}/{p.size}: {axioms}"

def publishStatement : MetaM Unit := withCurrents fun c => do
  let equality := mkAppN (mkConst ``Eq [.one]) #[c.functionType,c.primary,c.normalized]
  save statementName c.selected equality (mkSort .zero) true

def publishProof : MetaM Unit := withCurrents fun c => do
  let proof := mkAppN (mkConst ``Eq.refl [.one]) #[c.functionType,c.normalized]
  save proofName c.selected proof (app statementName c.selected) false

end JanetCartan.RevisedUniform.OriginalStepFields.PrimaryCurrentTemplate
end
