module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalTransferTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Actual instantiation of original primary-strain aggregation

Supply the proved original node bound at every actual sample. All analytic
inputs are thus closed for the same physical field (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalActualTemplate
open Lean Meta Elab Command
open FinalTransferTemplate

elab "instantiate_primary_strain_from_original_nodes" : command => liftTermElabM do
  withInputs fun d q hOp δ hδ => do
    let node := app (family ++ `node_strain_bound)
      (d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample])
    let nodes ← mkLambdaFVars #[d.sample] node
    let p := parameters d q hOp δ hδ
    publish `strain_bound p (app (root ++ `strain_of_original_nodes) (p.push nodes))
      (app (root ++ `strain_statement) p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FinalActualTemplate
end
