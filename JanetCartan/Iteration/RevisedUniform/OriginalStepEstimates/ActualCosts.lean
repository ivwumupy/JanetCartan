module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ConditionedCosts
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainCosts
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.CostPublicationTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The actual step coefficient before the history

Substitute the original primary strain price into the already constructed
common coefficient. Its nine original source prices, the exact high norm
price and the fixed background price are unchanged. This static leaf does
not assert a step estimate (`main:thm:step`, `main:prop:current-scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

construct_actual_original_step_cost 0
construct_actual_original_step_cost 1

#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C_nonneg
