module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Actual instantiation of the original primary-node strain bound

The full-family pointwise discrepancy estimate and its proved nonnegative
coefficient supply every analytic input of the separately checked node
transfer. The result is the original aggregation premise for the identical
sampled complex node (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualTemplate

open Lean Meta Elab Command
open FamilyTemplate

elab "instantiate_actual_primary_node" : command => liftTermElabM do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le
        #[app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Sop d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp => do
        let fixed := d.fixed.push q
        let C := app (root ++ `Cdiscrepancy) fixed
        let hC := app (root ++ `Cdiscrepancy_nonneg) fixed
        let hUniform := app (root ++ `actual_uniform_discrepancy) fixed
        let args := d.selected[:33].toArray ++ #[d.steps,q,C,hC,hUniform] ++
          d.selected[33:].toArray ++ #[d.hAux,hOp,d.sample]
        unless args.size == 60 do
          throwError "actual primary node: original uniform-transfer telescope changed"
        let proof := app
          `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.node_of_uniform_discrepancy args
        let p := d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample]
        let proof ← mkAppM ``Eq.mp #[app (root ++ `uniform_node_statement_eq) p,proof]
        save `node_strain_bound p proof (app (root ++ `node_strain_statement) p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualTemplate
end
