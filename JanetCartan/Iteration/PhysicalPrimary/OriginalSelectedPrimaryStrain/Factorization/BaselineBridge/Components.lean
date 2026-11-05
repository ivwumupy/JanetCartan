module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineData
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# Exact names for the original raw baseline components

Both function equalities close at the original outer56, before the nonzero
outer-weight proof and source point. The proof uses reflexivity of the compact
published name; the native expansion occurs only in its independently checked
predicate. Consumer: `Actual.baseline_factor` (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template

open Lean Meta

private def publishComponent (isAmplitude statement : Bool) : MetaM Unit := do
  let predicate := root ++ (if isAmplitude then `amplitude_statement else `wave_statement)
  let endpoint := root ++ (if isAmplitude then `amplitude_eq_native else `wave_eq_native)
  if statement then
    -- These exact component deductions need only the already proved raw
    -- theorem; they do not wait for its new named predicate to be published.
    withNative fun all _ target => do
      let c ← parts all target
      let p := c.params[:56].toArray
      let named := app (if isAmplitude then baseline ++ `baseline else actual ++ `baseline_wave) p
      let native ← if isAmplitude then mkLambdaFVars #[c.params[57]!] c.amplitude else pure c.field
      let type ← typeAt named
      let equation := mkAppN (mkConst ``Eq [.one]) #[type, named, native]
      save predicate p equation (mkSort .zero) true
  else
    withStoredTelescope predicate 56 fun p _ => do
      let equation ← bodyAt (app predicate p)
      unless equation.isAppOfArity ``Eq 3 do
        throwError "raw baseline bridge: original component predicate changed"
      let a := equation.getAppArgs
      let proof := mkAppN (mkConst ``Eq.refl equation.getAppFn.constLevels!) #[a[0]!, a[1]!]
      save endpoint p proof (app predicate p)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge.Template
end
