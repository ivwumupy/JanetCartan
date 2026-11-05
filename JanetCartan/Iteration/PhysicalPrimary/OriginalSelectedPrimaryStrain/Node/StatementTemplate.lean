module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalStrain
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # The exact original aggregation premise for one primary node

The node statement is the original finite-sampling theorem's own premise,
specialized to the actual sample and the proved fixed node coefficient.
This retains its original complex node, core and carrier decay without
expanding the tensor-transfer implementation (`main:eq:primary-strain`).
The actual node proof is supplied in the separate `Node` module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeStatementTemplate

open Lean Meta Elab Command
open FamilyTemplate

/-- Read the original all-sample premise at the actual sample. The amplitude
and its nonnegativity proof must disappear from this node statement; no
special amplitude is substituted to make that independence hold. -/
def requirement (d : RawProfilesTemplate.Data) (q C hC : Expr) : MetaM Expr :=
  withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
    let hδType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,δ]
    withLocalDeclNoLocalInstanceUpdate `hδ .default hδType fun hδ => do
      let source := d.sourceArgs[:52].toArray
      let args := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
      let type ← resultAt
        `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary_strain_of_complex_strain args
      let .forallE _ nodeType _ _ := type.consumeMData |
        throwError "actual primary node statement: original aggregate premise changed"
      let .forallE _ sampleType body _ := (← whnf nodeType).consumeMData |
        throwError "actual primary node statement: original sample binder changed"
      unless ← isDefEq sampleType (← inferType d.sample) do
        throwError "actual primary node statement: different original sample type"
      let target := body.instantiate1 d.sample
      if (target.find? (fun e => e == δ || e == hδ)).isSome then
        throwError "actual primary node statement: original node premise depends on amplitude"
      return target

elab "publish_actual_primary_node_statement" : command => liftTermElabM do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le
        #[app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Sop d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp => do
        let fixed := d.fixed.push q
        let target ← requirement d q (app (root ++ `Cnode) fixed)
          (app (root ++ `Cnode_nonneg) fixed)
        let p := d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample]
        save `node_strain_statement p target (mkSort .zero) true
        setReducibilityStatus (root ++ `node_strain_statement) .reducible

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeStatementTemplate
end
