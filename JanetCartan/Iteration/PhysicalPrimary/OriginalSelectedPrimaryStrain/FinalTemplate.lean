module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.AssemblyBasic
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalStrain
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # The primary strain bound for the identical full-source physical field

The actual node estimate is summed with the original square-root sample
weights. The resulting fixed price and exact revised carrier power feed
`RevisedStage.increment_estimates_of_physicalSobolev_profiles.hstrainBound`.
Every source, inverse, phase, and coefficient input has its actual producer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
private def family := root ++ `Family
private def old := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def full := `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-source primary strain: late or unresolved operand in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking SAME full-source physical primary strain {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual main:eq:primary-strain for the SAME OriginalFullSourcePhysicalPrimary.field54 on its original closed core. The genuine full-forcing raw source, undoubled phase, first mask, negative moments, uncut inverse, full tensor transfer and original square-root-weight aggregation supply every analytic input. Cstrain at selected33+N+accuracy precedes history/target/smoothing; the initial auxiliary and exact graph reaches are numerical, and the existing Tpair supplies the latter at canonical data; δ is nonnegative."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual full-source primary strain: nonstandard axioms {name}: {ax}"
  logInfo m!"PASS SAME full-source physical primary strain {key}/{p.size}: {ax}"

/-- The fixed price is read from the original aggregation result under its exact
node-estimate binder. The cost and statement modes use this local binder; closure checks ensure
it cannot enter a published coefficient, nonnegativity proof or proposition.
The actual strain proof instantiates the proved original node estimate. -/
private def withNodeEstimate (d : RawProfilesTemplate.Data) (q hOp aggregate : Expr)
    (typeOnly : Bool) (next : Expr → MetaM Unit) : MetaM Unit := do
  if typeOnly then
    let type ← FamilyTemplate.resultAt aggregate.getAppFn.constName! aggregate.getAppArgs
    let .forallE _ nodeType _ _ := type.consumeMData |
      throwError "actual full-source primary strain: original node-estimate binder changed"
    withLocalDeclNoLocalInstanceUpdate `nodeEstimate .default nodeType next
  else
    let node := app (family ++ `node_strain_bound)
      (d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample])
    next (← mkLambdaFVars #[d.sample] node)

elab "prove_actual_full_source_primary_strain " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 3 do throwError "actual full-source primary strain: unknown mode"
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le #[app (root ++ `Sop) d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp => do
        let fixed := d.fixed.push q
        let C := app (family ++ `Cnode) fixed
        let hC := app (family ++ `Cnode_nonneg) fixed
        withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
          let hδType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,δ]
          withLocalDeclNoLocalInstanceUpdate `hδ .default hδType fun hδ => do
            let source := d.sourceArgs[:52].toArray
            let p := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
            let aggregate := app (old ++ `selectedSourcePrimary_strain_of_complex_strain) p
            withNodeEstimate d q hOp aggregate (mode.getNat != 2) fun nodes => do
              let bound := mkApp aggregate nodes
              forallBoundedTelescope (← inferType bound) (some 2) fun point inequality => do
                unless point.size == 2 && inequality.isAppOfArity ``LE.le 4 do
                  throwError "actual full-source primary strain: original core estimate changed"
                let rhs := inequality.getAppArgs[3]!
                unless rhs.isAppOfArity ``HMul.hMul 6 && rhs.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do
                  throwError "actual full-source primary strain: original sampled price disappeared"
                let price := rhs.getAppArgs[4]!.getAppArgs[4]!
                if mode.getNat == 0 then
                  save `Cstrain fixed price (mkConst ``Real) true
                  return
                if mode.getNat == 1 then
                  unless price.isAppOfArity ``HMul.hMul 6 &&
                      price.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 &&
                      price.getAppArgs[5]!.isAppOfArity ``Real.sqrt 1 do
                    throwError "actual full-source primary strain: fixed square-root weight cost changed"
                  let lhs := price.getAppArgs[4]!.getAppArgs[4]!
                  unless lhs.isAppOfArity ``Real.sqrt 1 do
                    throwError "actual full-source primary strain: original real quadrature factor changed"
                  let proof ← mkAppM ``mul_nonneg
                    #[← mkAppM ``mul_nonneg #[← mkAppM ``Real.sqrt_nonneg #[lhs.appArg!],hC],
                      ← mkAppM ``Real.sqrt_nonneg #[price.getAppArgs[5]!.appArg!]]
                  let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,app (root ++ `Cstrain) fixed]
                  save `Cstrain_nonneg fixed proof target
                  return
                let powers := rhs.getAppArgs[5]!
                unless powers.isAppOfArity ``HMul.hMul 6 do
                  throwError "actual full-source primary strain: original powers changed"
                let ordinaryPower := powers.getAppArgs[4]!
                unless ordinaryPower.isAppOfArity ``HPow.hPow 6 do
                  throwError "actual full-source primary strain: original stage power disappeared"
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
                let named := app (full ++ `field) (d.selected ++ #[d.steps,δ])
                let target := (← inferType proof).replace fun e =>
                  if e.isAppOfArity (old ++ `selectedSourcePrimary) 53 then some named else none
                unless (target.find? (· == named)).isSome do
                  throwError "actual full-source primary strain: SAME full-source field was not retained"
                let p := d.selected ++ #[d.hAux,hOp,d.steps,q,δ,hδ]
                if mode.getNat == 3 then
                  save `strain_statement p (← mkForallFVars point target) (mkSort .zero) true
                  setReducibilityStatus (root ++ `strain_statement) .reducible
                else
                  save `strain_bound p (← mkLambdaFVars point proof)
                    (app (root ++ `strain_statement) p)
end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTemplate
end
