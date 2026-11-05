module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.AssemblyBasic
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Original-node aggregation for the identical physical primary

This deduction assumes precisely the original node statement for every
original sample. It retains the fixed Cstrain, physical field54 and revised
carrier exponent. The actual final producer supplies the proved node estimates
separately (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTransferTemplate

open Lean Meta Elab Command

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
def family := root ++ `Family
def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

def withInputs
    (next : RawProfilesTemplate.Data → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le #[app (root ++ `Sop) d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp =>
        withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
          let hδType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,δ]
          withLocalDeclNoLocalInstanceUpdate `hδ .default hδType fun hδ =>
            next d q hOp δ hδ

def parameters (d : RawProfilesTemplate.Data) (q hOp δ hδ : Expr) : Array Expr :=
  d.selected ++ #[d.hAux,hOp,d.steps,q,δ,hδ]

def publish (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original primary aggregation: unresolved or late operand in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original primary aggregation {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original square-root-weight aggregation on the SAME FullSourcePhysicalPrimary.field54, with fixed Cstrain35 and the exact revised carrier exponent (main:eq:primary-strain). The conditional deduction takes the original all-sample node statement; the actual strain_bound supplies its proven original-data producer."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original primary aggregation: nonstandard axioms {name}: {ax}"
  logInfo m!"PASS original primary aggregation {key}/{p.size}: {ax}"

private def openPoint (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop 2 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p type
    | k+1, type, p => do
      let .forallE name domain body bi := (← whnf type).consumeMData |
        throwError "original primary aggregation: original point tail changed"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        loop k (body.instantiate1 x) (p.push x)

elab "prove_primary_strain_from_original_nodes" : command => liftTermElabM do
  withInputs fun d q hOp δ hδ => do
    let fixed := d.fixed.push q
    let C := app (family ++ `Cnode) fixed
    let hC := app (family ++ `Cnode_nonneg) fixed
    let nodeArgs := d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample]
    let nodeType ← mkForallFVars #[d.sample] (app (family ++ `node_strain_statement) nodeArgs)
    withLocalDeclNoLocalInstanceUpdate `hNodes .default nodeType fun hNodes => do
      let source := d.sourceArgs[:52].toArray
      let args := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
      let aggregate := app
        `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary_strain_of_complex_strain args
      let bound := mkApp aggregate hNodes
      openPoint (← inferType bound) fun point inequality => do
        unless inequality.isAppOfArity ``LE.le 4 do
          throwError "original primary aggregation: original point inequality changed"
        let rhs := inequality.getAppArgs[3]!
        unless rhs.isAppOfArity ``HMul.hMul 6 && rhs.getAppArgs[5]!.isAppOfArity ``HMul.hMul 6 do
          throwError "original primary aggregation: original sampled powers changed"
        let ordinaryPower := rhs.getAppArgs[5]!.getAppArgs[4]!
        unless ordinaryPower.isAppOfArity ``HPow.hPow 6 do
          throwError "original primary aggregation: original stage power disappeared"
        let R := ordinaryPower.getAppArgs[4]!
        let exponent := ordinaryPower.getAppArgs[5]!
        let hR₀ ← mkAppM ``le_trans
          #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS d.native[:44].toArray,d.native[45]!]
        let facts ← mkAppM ``JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hR₀,d.native[46]!]
        let hR ← mkAppM ``lt_of_lt_of_le
          #[← mkAppOptM ``zero_lt_one #[some (mkConst ``Real),none,none,none,none,none],
            FamilyTemplate.part facts 0]
        let equality := app ``combine_strain_powers
          #[R,hR,app (root ++ `Cstrain) fixed,δ,exponent,mkConst ``JanetCartan.carrierExponent,q]
        let proof ← mkAppM ``le_of_le_of_eq #[mkAppN bound point,equality]
        let named := app `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
          (d.selected ++ #[d.steps,δ])
        let checked := (← inferType proof).replace fun e =>
          if e.isAppOfArity
              `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary 53 then
            some named else none
        unless (checked.find? (· == named)).isSome do
          throwError "original primary aggregation: SAME physical field was lost"
        let p := parameters d q hOp δ hδ
        publish `strain_of_original_nodes (p.push hNodes) (← mkLambdaFVars point proof)
          (app (root ++ `strain_statement) p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTransferTemplate
end
