module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.CostPublicationTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Statement
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The common original coefficient with the primary strain price explicit

The original norm, signed-lag, smoothing and frame prices are fixed before
the history. Only the primary strain price awaits substitution from
`OriginalSelectedPrimaryStrain.Cstrain`. This coefficient alone does not
assert a step estimate (`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_original_early_step_cost 0
publish_original_early_step_cost 1

#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C_of_primary_strain
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C_of_primary_strain_nonneg
