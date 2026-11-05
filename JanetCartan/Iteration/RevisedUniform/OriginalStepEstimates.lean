module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepFields
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualCosts
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Conditioned
public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.StrainTransport
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.PrimaryOperatorGate
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainStatement
import all JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.ActualBasics
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The actual original-data finite physical step

The original primary strain producer closes the final input to the same
physical step. The fixed coefficient and threshold precede every history and
target dilation. The resulting single Schwartz increment has the exact v2
band, displacement and metric-error estimates (`main:thm:step`).

The consumer is the original `RevisedGlobal.UniformHistoryCorrection`, which
supplies the iteration in `main:prop:current-scale` and `main:thm:main`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

prove_actual_original_step

#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.C_nonneg
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.T
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.T_reaches
#print axioms JanetCartan.RevisedUniform.OriginalStepEstimates.step
