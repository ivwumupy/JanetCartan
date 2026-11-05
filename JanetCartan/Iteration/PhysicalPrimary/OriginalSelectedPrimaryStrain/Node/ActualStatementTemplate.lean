module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Equality of the two original primary-node statements

At the actual discrepancy coefficient, the uniform transfer's original
aggregation premise is the published node statement with the identical
coefficient, field, core and carrier decay (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualStatementTemplate

open Lean Meta Elab Command
open FamilyTemplate

elab "identify_actual_primary_node_statement" : command => liftTermElabM do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le
        #[app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Sop d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp => do
        let fixed := d.fixed.push q
        let C := app (root ++ `Cdiscrepancy) fixed
        let left := app
          `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.node_strain_statement
          (d.args ++ #[q,C])
        let p := d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample]
        let right := app (root ++ `node_strain_statement) p
        save `uniform_node_statement_eq p (← mkEqRefl left) (← mkEq left right)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualStatementTemplate
end
