module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ConditionedCosts
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfiles
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairProfiles.Nonnegative
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairCore.Metric
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ConditionedTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Statement
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The original physical step with precisely its primary strain input open

The same original mean, signed correction, primary norm and two smoothing
tails are instantiated internally. The remaining primary strain bound has
the exact field, exponent and initial numerical reach of
`OriginalSelectedPrimaryStrain.strain_bound`. Its coefficient precedes the
history. The actual root must substitute that producer before claiming the
uniform correction or Theorem 1.1 (`main:thm:step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_original_step_of_primary_strain

#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.step_of_primary_strain
