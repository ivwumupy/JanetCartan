module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Observation
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.SumSource
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Composition
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# The final exact source transport

The exact two-transitivity composition is checked separately. Its derivative
identity input is supplied here by `observed_field_eq56`. The original prefix
identity is the sole remaining input, supplied by `Actual.prefixed_forward`
in the parent source application (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Transport

open Lean Meta

private def closeSource : MetaM Unit :=
  Template.withInputs fun c => do
    let root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge
    let factor := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
    let app := SourceTemplate.app
    let p := c.data.params.push c.point[0]!
    let all := c.data.params ++ c.point
    withLocalDeclD `hPrefixed c.prefixed fun forward => do
      let observed := app (root ++ `observed_field_eq) p
      let proof := app (root ++ `observed_from_prefix_and_field) (all ++ #[forward, observed])
      Template.save (factor ++ `observed_raw_angular_of_prefixed) (all.push forward) proof
        (app (factor ++ `observed_raw_angular_statement) all)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Transport
end
