module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.ObservationStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! The SAME whole raw angular field gives the SAME original observed
derivative by congruence. No smoothness or new chart assumption is needed
for this field equality. Consumer: the source58 bridge (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

meta section
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization

run_meta do
  let root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge
  SourceBridge.Template.withInputs fun c => do
    let fieldEq ← SourceTemplate.bodyAt (SourceTemplate.app (root ++ `field_statement) c.data.params)
    unless fieldEq.isAppOfArity ``Eq 3 do
      throwError "source observation: original field identity changed"
    let f := fieldEq.getAppArgs
    let a := c.prefixEq.getAppArgs
    let context ← withLocalDeclD `rawField f[0]! fun v =>
      mkLambdaFVars #[v] (a[1]!.replace fun e => if e == c.prefixField then some v else none)
    let proof := mkAppN (mkConst ``congrArg [.one, .one])
      #[f[0]!, a[0]!, f[1]!, f[2]!, context, SourceTemplate.app (root ++ `field_eq) c.data.params]
    let p := c.data.params.push c.point[0]!
    SourceBridge.Template.save (root ++ `observed_field_eq) p proof
      (SourceTemplate.app (root ++ `observed_field_statement) p)

end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.observed_field_eq
