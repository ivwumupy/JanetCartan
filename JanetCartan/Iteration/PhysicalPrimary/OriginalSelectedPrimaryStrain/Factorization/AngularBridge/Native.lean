module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The already proved native raw derivative, specialized to its exact
actual53 parameters before the named-field conversion. This is an equality,
not a derivative premise (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawPrimaryRealizationApplication

elab "specialize_original_raw_angular_native " mode:num : command => liftTermElabM do
  withNode fun p _ tail proof => do
    let all := p ++ tail
    if mode.getNat == 0 then
      save `native_forward_statement all (← inferType proof) (mkSort .zero) true
    else if mode.getNat == 1 then
      save `native_forward all proof (app (root ++ `native_forward_statement) all)
    else throwError "raw angular bridge: unknown native specialization"

specialize_original_raw_angular_native 0
specialize_original_raw_angular_native 1

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
