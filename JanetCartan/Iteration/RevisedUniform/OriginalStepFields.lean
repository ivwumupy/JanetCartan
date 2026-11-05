module

public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepFields.Template
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The original common primary, mean and signed correction

The data of the single physical step in `paper-v2.tex`, `main:thm:step`.
All fields use the same selected history, full forcing, sample and finite
Picard count. `primary`, `mean`, `fullSelf`, `offSelf` and `meanError` take
selected52 and the common count. `signedCorrection`, `secondary` and
`increment` additionally take the original pair scale and numerical window
certificate. The final increment is the existing real Fourier cutoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

construct_original_step_field 0
construct_original_step_field 1
construct_original_step_field 2
construct_original_step_field 3
construct_original_step_field 4
construct_original_step_field 5
construct_original_step_field 6
construct_original_step_field 7
