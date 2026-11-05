module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.PhaseStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The SAME native retained phase in the actual source coordinates.
Consumer: the original raw source factorization (main:eq:primary-strain). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
open Lean Meta Elab Command

run_cmd liftTermElabM do
  let statement := root ++ `native_phase.statement
  withStoredTelescope statement 53 fun p _ => do
    let info ← getConstInfo statement
    let eq := (info.value! (allowOpaque := true)).beta p
    unless eq.isAppOfArity ``Eq 3 do
      throwError "raw angular bridge: exact Phase proposition changed"
    -- The named actual side has an already checked compact application.
    -- Reflexivity still proves the identical native-to-actual equality.
    save `native_phase_eq_actual p (← mkEqRefl eq.getAppArgs[2]!) (app statement p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end

