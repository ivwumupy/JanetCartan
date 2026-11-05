module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.AssembleTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public meta import Lean

/-!
# The exact primary-strain input on the original common core

This names the existing component consumer's pointwise input at the same
selected52 and full-source field54. The scalar remains an explicit argument;
the definition asserts no estimate. A separate generic-source transport
will apply the actual raw strain and current identity before the large
dimension/metric specialization (`main:eq:primary-strain`, `main:thm:step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepStrainInputTemplate

open Lean Meta Elab Command
open OriginalStepEstimatesTemplate

def root : Name := `JanetCartan.RevisedUniform.OriginalStepEstimates
def strainRoot : Name := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | value => value

def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "original strain input: unavailable body {key}"
  pure (head (value.beta p))

/-- Expression metadata only; it is not a mathematical hypothesis record. -/
structure Data where
  parameters : Array Expr
  selected : Array Expr
  native : Array Expr
  source : Array Expr
  n : Expr
  targetDimension : Expr
  primary : Expr
  rawCurrent : Expr
  current : Expr
  core : Expr
  rawStatement : Expr
  rawPointwise : Expr
  cost : Expr

def inputArguments (d : Data) (Cstrain : Expr) : Array Expr :=
  d.selected ++ #[d.parameters[54]!,d.parameters[55]!,d.parameters[56]!,Cstrain]

def inputType (d : Data) (Cstrain : Expr) : MetaM Expr :=
  originalStrainInputType d.n d.targetDimension d.current d.primary d.core Cstrain
    d.parameters[56]! d.source[4]! d.parameters[55]!

private partial def withArguments (type : Expr) (remaining : Nat)
    (p : Array Expr) (next : Array Expr → MetaM Unit) : MetaM Unit := do
  if remaining == 0 then
    next p
  else
    let .forallE name domain body bi := type.consumeMData
      | throwError "original strain input: changed frozen statement58 parameters"
    withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
      withArguments (body.instantiate1 x) (remaining - 1) (p.push x) next

/-- Read the frozen actual statement and field definitions at generic
selected data. No history, target or source is replaced. -/
def withData (next : Data → MetaM Unit) : MetaM Unit := do
  let statement := strainRoot ++ `strain_statement
  withArguments (← getConstInfo statement).type 58 #[] fun p => do
    let selected := p[:52].toArray
    let rawStatement := app statement p
    let rawPointwise ← bodyAt statement p
    let .forallE _ _ rest _ := rawPointwise
      | throwError "original strain input: missing original physical point"
    let .forallE _ _ atom _ := head rest
      | throwError "original strain input: missing original physical-core membership"
    let some linear := atom.find? (·.isAppOfArity `JanetCartan.linearizedMetric 5)
      | throwError "original strain input: missing exact linearized metric"
    let lin := linear.getAppArgs
    for e in #[lin[0]!,lin[1]!,lin[2]!] do
      if e.hasLooseBVars then
        throwError "original strain input: current or dimension depends on the point"
    let source ← bodyAt `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget selected
    unless source.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
      throwError "original strain input: changed normalized source10"
    let a := source.getAppArgs
    let primary := app `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
      (selected ++ #[p[54]!,p[56]!])
    let rawPrimary ← bodyAt primary.getAppFn.constName! primary.getAppArgs
    unless rawPrimary.isAppOfArity
        `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary 53 do
      throwError "original strain input: changed original full-source primary53"
    let native := rawPrimary.getAppArgs[:50].toArray
    let current := app `JanetCartan.RevisedGlobal.finiteMap
      #[lin[0]!,lin[1]!,a[2]!,a[8]!,a[9]!]
    let core := app `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore.core
      native[:44].toArray
    let cost := app (strainRoot ++ `Cstrain) (selected[:33].toArray ++ #[p[54]!,p[55]!])
    next
      { parameters := p
        selected := selected
        native := native
        source := a
        n := lin[0]!
        targetDimension := lin[1]!
        primary := primary
        rawCurrent := lin[2]!
        current := current
        core := core
        rawStatement := rawStatement
        rawPointwise := rawPointwise
        cost := cost }

def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  unless p.size == (if data then 56 else 59) do
    throwError "original strain input: an extra producer assumption entered {key}/{p.size}"
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original strain input: extra or unresolved data in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "original strain input: unavailable original metadata {missing.toList}"
  let name := root ++ key
  if (env.find? name).isSome then throwError "original strain input: duplicate declaration {name}"
  IO.println s!"Checking exact original primary strain input {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
    setReducibilityStatus name .reducible
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact existing physical-step primary strain input for the original full-source field54 on the original common core, with its same selected52 and Picard count. A transparent proposition names the input without asserting it; the generic transport must use the actual raw strain and original current identity before the dimension/metric specialization (main:eq:primary-strain; main:thm:step)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original strain input: nonstandard axioms {axioms}"
  logInfo m!"PASS exact original primary strain input {key}/{p.size}: {axioms}"

elab "define_original_primary_strain_input" : command => liftTermElabM do
  withData fun d => do
    withLocalDeclNoLocalInstanceUpdate `Cstrain .default (mkConst ``Real) fun Cstrain => do
      save `primary_strain_input (inputArguments d Cstrain) (← inputType d Cstrain) (mkSort .zero) true

end JanetCartan.RevisedUniform.OriginalStepStrainInputTemplate
end
