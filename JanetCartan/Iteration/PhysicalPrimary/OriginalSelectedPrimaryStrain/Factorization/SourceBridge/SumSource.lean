module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.SumSourceStatement
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! Compose only the two exact original annular identities; no derivative
field context is rechecked here. Consumer: the source58 bridge
(`main:eq:primary-strain`). -/

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
    let p := c.data.params.push c.point[0]!
    let proof := mkAppN (mkConst ``Eq.trans c.prefixEq.getAppFn.constLevels!)
      #[a[0]!, a[2]!, b[1]!, b[2]!, SourceTemplate.app (root ++ `rhs_eq_grouped) p, c.groupedProof]
    SourceBridge.Template.save (root ++ `sum_eq_source) p proof
      (SourceTemplate.app (root ++ `sum_source_statement) p)

end

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceBridge.sum_eq_source
