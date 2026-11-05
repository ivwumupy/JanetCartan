module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceForwardStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Field
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! The original observed derivative changes only its raw-field name. Its
exact producer is congruence of `field_eq55`; the consumer is the unchanged
`observed_raw_angular_of_prefixed58` (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization

run_meta do
  let factor := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
  SourceBridge.Template.withInputs fun c => do
    let all := c.data.params ++ c.point
    let original ← SourceTemplate.bodyAt
      (SourceTemplate.app (factor ++ `observed_raw_angular_statement) all)
    unless original.isAppOfArity ``Eq 3 do
      throwError "source observation: original source target changed"
    let a := c.prefixEq.getAppArgs
    let target := mkAppN (mkConst ``Eq c.prefixEq.getAppFn.constLevels!)
      #[a[0]!, a[1]!, original.getAppArgs[1]!]
    SourceBridge.Template.save (factor ++ `SourceBridge.observed_field_statement)
      (c.data.params.push c.point[0]!) target (mkSort .zero) true

end
