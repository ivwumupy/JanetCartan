module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.PairedStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.NativePairedStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.NativeNodeStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.PairedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.NativePairedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.NativeNodeStatement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Exact selected and native predicates for the original primary node

The paired-source bound and the aggregate node conclusion are already named
on both original-data interfaces. Retain their proposition equalities at
selected52,N,sample,accuracy,C, specializing the native predicates to the SAME
sourceArgs53. No auxiliary profile, operator gate, frame tolerance or source
estimate is an input to these identities. Consumer: `NodeUniformTransfer`,
which transports its selected source bound into the native node deduction
and transports the conclusion back (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeSelectedNativeGlue.Template

open Lean Meta Elab Command

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeSelectedNativeGlue
def transferRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer
def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p

def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "selected/native node identity: missing saved body {info.name}"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta
    e.getAppArgs).headBeta

/-- The selected and native data arrays at the SAME Picard count, sample,
accuracy and price. The raw-profile admission is not a retained parameter. -/
def withParameters (next : Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let p := d.args ++ #[q,C]
        let native := d.sourceArgs ++ #[q,C]
        unless p.size == 56 && native.size == 55 do
          throwError "selected/native node identity: original parameter order changed"
        next p native

private def openRaw (count : Nat) (type : Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,_,p => next p
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "selected/native node identity: saved telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "selected/native node identity: unresolved or extra input in {key}"
    let missing := e.getUsedConstants.filter fun name => (env.find? name).isNone
    unless missing.isEmpty do
      throwError "selected/native node identity: missing original metadata {missing}"
    if e.getUsedConstants.any (fun name => name.toString.startsWith "Scratch." ||
        name.toString.startsWith "GoalNodeSelectedNative" || name.toString.startsWith "JanetCartan.Scratch.") then
      throwError "selected/native node identity: forbidden scratch dependency"
  let name := root ++ key
  if (env.find? name).isSome then throwError "selected/native node identity: duplicate {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Kernel checking exact selected/native node predicate {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The selected original paired-source predicate or original aggregate node predicate equals its native predicate at the SAME sourceArgs53. Inputs are exactly selected52,N,sample,accuracy,C; no auxiliary profile, operator/frame gate, nonnegativity proof or analytic estimate is added. The original full half-core, current, complex node, carrier decay and coefficient are preserved. Consumer: NodeUniformTransfer (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "selected/native node identity: nonstandard axioms {axioms}"
  logInfo m!"PASS exact selected/native node predicate {key}/{p.size}: {axioms}"

def publishStatement (node : Bool) : MetaM Unit :=
  withParameters fun p native => do
    let selectedKey := if node then `node_strain_statement else `paired_discrepancy_bound
    let nativeKey := if node then `native_node_strain_statement else `native_paired_discrepancy_bound
    let left := app (transferRoot ++ selectedKey) p
    let right := app (transferRoot ++ nativeKey) native
    let equality := mkAppN (mkConst ``Eq [.succ .zero]) #[mkSort .zero,left,right]
    save (if node then `node_statement else `paired_statement) p equality (mkSort .zero) true

def publishProof (node : Bool) : MetaM Unit := do
  let statementName := root ++ (if node then `node_statement else `paired_statement)
  openRaw 56 (← getConstInfo statementName).type fun p => do
    let target := app statementName p
    let equality ← bodyAt target
    unless equality.isAppOfArity ``Eq 3 && equality.getAppArgs[0]! == mkSort .zero do
      throwError "selected/native node identity: saved proposition equality changed"
    let a := equality.getAppArgs
    let proof := mkAppN (mkConst ``Eq.refl equality.getAppFn.constLevels!) #[a[0]!,a[1]!]
    save (if node then `node_eq else `paired_eq) p proof target false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeSelectedNativeGlue.Template
end
