module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.ResidualIdentity
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.AssemblyBasic
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Inputs
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Labels
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalStatement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! Exact original data for the conditional node transfer. The sole analytic
input is one uniform pointwise discrepancy bound over the complete original
ObservedLabels family (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.Template
open Lean Meta Elab Command
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain

def primaryRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
def familyRoot := primaryRoot ++ `Family
def sourceRoot := primaryRoot ++ `SourceData
def transferRoot := primaryRoot ++ `StrainTransfer
def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p

def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "node join review: unavailable exact body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

def selectedInequality (type : Expr) : MetaM Expr := do
  let mut result := type
  for key in #[transferRoot ++ `selected_node_strain_le_discrepancies_statement,
      transferRoot ++ `native_node_strain_le_discrepancies_statement] do
    unless result.isAppOfArity key 56 do
      throwError "node join review: changed exact selected/native statement head"
    result ← bodyAt result
  unless result.isAppOfArity ``LE.le 4 do
    throwError "node join review: not the original complex strain inequality"
  return result

def labelAt (d : RawProfilesTemplate.Data) (q hOp : Expr) : Expr :=
  app (primaryRoot ++ `observedLabel) (d.profileArgs ++ #[q,hOp])

def rhoAt (d : RawProfilesTemplate.Data) : MetaM Expr := do
  let R := app ``JanetCartan.historyScale
    #[d.native[44]!,mkConst ``JanetCartan.growthExponent,d.native[46]!]
  mkAppM ``HPow.hPow #[R,mkConst ``JanetCartan.carrierExponent]

def decayAt (rho q : Expr) : MetaM Expr := do
  let qr ← mkAppOptM ``Nat.cast #[some (mkConst ``Real),none,some q]
  let neg ← mkAppM ``Neg.neg #[qr]
  mkAppM ``HPow.hPow #[rho,neg]

def withOperator (next : RawProfilesTemplate.Data → Expr → MetaM Unit) : MetaM Unit :=
  DataTemplate.withData fun d => do
    let gate ← mkAppM ``LE.le
      #[app (primaryRoot ++ `Sop) d.selected[:33].toArray,d.native[44]!]
    withLocalDeclNoLocalInstanceUpdate `hOp .default gate fun hOp => next d hOp

def uniformType (d : RawProfilesTemplate.Data) (q C : Expr)
    (point : Array Expr) : MetaM Expr := do
  let labels := app (primaryRoot ++ `ObservedLabels) d.fixed
  withLocalDeclNoLocalInstanceUpdate `sourceLabel .default labels fun t => do
    let value := mkApp (app (familyRoot ++ `discrepancy) (d.fixed.push t)) point[0]!
    let norm ← mkAppM ``Norm.norm #[value]
    let rho := app (familyRoot ++ `frequency) (d.fixed.push t)
    let price ← mkAppM ``HMul.hMul #[C,← decayAt rho q]
    let bound ← mkAppM ``LE.le #[norm,price]
    mkForallFVars #[t] (← mkForallFVars point bound)

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer

def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "node uniform transfer: unresolved or additional premise in {key}"
    if e.getUsedConstants.any (fun c => c.toString.startsWith "Scratch." ||
        c.toString.startsWith "GoalNodeTransferReview" || c.toString.startsWith "JanetCartan.Scratch.") then
      throwError "node uniform transfer: forbidden Scratch dependency"
    let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
    unless missing.isEmpty do throwError "node uniform transfer: missing original metadata {missing.toList}"
    for prohibited in #[familyRoot ++ `discrepancy_bound,familyRoot ++ `Cdiscrepancy,
        familyRoot ++ `node_strain_bound] do
      if e.getUsedConstants.contains prohibited then
        throwError "node uniform transfer: unfinished producer was used"
  let name := root ++ key
  if (env.find? name).isSome then throwError "node uniform transfer: duplicate declaration {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Kernel checking original conditional node transfer {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Exact original complete-family node transfer data or deduction. The selected source, original uncut response, undoubled carrier and half-core are retained; only the displayed full-family discrepancy bound and its nonnegative price are analytic inputs (main:eq:primary-strain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "node uniform transfer: nonstandard axioms {ax}"
  logInfo m!"PASS original conditional node transfer {key}/{p.size}: {ax}"

def openRaw (count : Nat) (type : Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,_,p => next p
    | k+1,type,p => do
      let .forallE key domain body bi := type.consumeMData |
        throwError "node uniform transfer: published telescope ended at {p.size}"
      withLocalDeclNoLocalInstanceUpdate key bi (domain.instantiateRev p) fun x =>
        loop k body (p.push x)


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.Template
end
