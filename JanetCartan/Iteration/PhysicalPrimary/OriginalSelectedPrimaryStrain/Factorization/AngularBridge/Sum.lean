module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Phase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Amplitude
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.SumTransport
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! Discharge the exact phase and amplitude equalities in the original
annular-sum transport. No additional premise remains in the actual source
factorization (main:eq:primary-strain). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
open Lean Meta Elab Command

elab "close_original_raw_angular_sum" : command => liftTermElabM do
  withStoredTelescope (root ++ `native_rhs_of_phase_amplitude) 55 fun p _ => do
    let actualParams := p[:53].toArray
    let all := p ++ #[app (root ++ `native_phase_eq_actual) actualParams,
      app (root ++ `native_amplitude_eq_actual) actualParams]
    let proof := app (root ++ `native_rhs_of_phase_amplitude) all
    let target ← storedType (root ++ `native_rhs_of_phase_amplitude) all
    save `native_rhs_eq_actual_sum p proof target

close_original_raw_angular_sum

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
