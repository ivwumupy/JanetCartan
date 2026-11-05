module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepFields.PrimaryCurrent.Statement
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepFields.PrimaryCurrent.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The original dilated reference and its FlatReference map give the same
finite current. This supplies the actual primary input of the step without a
new current-equality hypothesis (`main:thm:step`). -/

set_option warningAsError true
set_option Elab.async false

run_meta JanetCartan.RevisedUniform.OriginalStepFields.PrimaryCurrentTemplate.publishProof

#print axioms JanetCartan.RevisedUniform.OriginalStepFields.primary_current_eq_normalized_history
