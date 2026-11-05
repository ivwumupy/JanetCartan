module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Rhs
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! The literal original prefix sum equals the SAME raw source field.
Its producers are `rhs_eq_grouped56` and the original `RawGrouped` identity;
its consumer is the source58 bridge (`main:eq:primary-strain`). -/

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
    let a := c.prefixEq.getAppArgs
    let b := c.groupedEq.getAppArgs
    let target := mkAppN (mkConst ``Eq c.prefixEq.getAppFn.constLevels!) #[a[0]!, a[2]!, b[2]!]
    SourceBridge.Template.save (root ++ `sum_source_statement) (c.data.params.push c.point[0]!)
      target (mkSort .zero) true

end
