module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Actual source input of the primary-node transfer

The already proved full-family discrepancy bound supplies the transfer's
uniform source predicate at its identical chosen coefficient. This separate
proof makes the real analytic instantiation explicit before the node transfer
is applied (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualHypothesisTemplate

open Lean Meta Elab Command
open FamilyTemplate

elab "admit_actual_primary_node_source" : command => liftTermElabM do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let fixed := d.fixed.push q
      let C := app (root ++ `Cdiscrepancy) fixed
      let target := app
        `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.uniform_discrepancy_bound
        (fixed.push C)
      save `actual_uniform_discrepancy fixed (app (root ++ `discrepancy_bound) fixed) target

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeActualHypothesisTemplate
end
