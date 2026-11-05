module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Syntax
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The exact native-to-actual annular-sum equality. Both sides are read
from the already checked native and actual derivative propositions; no
phase, input, amplitude or source chart is reselected (main:eq:primary-strain). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
open Lean Meta Elab Command

elab "retain_original_actual_raw_sum_statement" : command => liftTermElabM do
  withStoredTelescope (actual ++ `unprefixed_forward_statement) 56 fun all _ => do
    let nativeInfo ← getConstInfo (root ++ `native_forward_statement)
    let actualInfo ← getConstInfo (actual ++ `unprefixed_forward_statement)
    let nt := (nativeInfo.value! (allowOpaque := true)).beta all
    let actualType := (actualInfo.value! (allowOpaque := true)).beta all
    unless nt.isAppOfArity ``Eq 3 && actualType.isAppOfArity ``Eq 3 do
      throwError "raw angular bridge: the exact original derivative predicates changed"
    let target ← mkEq nt.getAppArgs[2]! actualType.getAppArgs[2]!
    save `actual_sum_statement all[:55].toArray target (mkSort .zero) true

retain_original_actual_raw_sum_statement

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end
