module

public import JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupport
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# Actual whole-parent outer-weighted Hermitian profiles

The literal unscaled baseline is `OriginalBackgroundHermitian.H`: the existing
common measurement applied to the full corrected derivative amplitude at the
genuine carrier graph. Its only weight is the existing outer `ψ = χouter²`.
The measurement compact and outer support lie in the ORIGINAL parent cell.
No inner carrier extension, coefficient cutoff, Fourier scalar or angular
modulation is used in this module.

`D` has only common44 plus row, before R/history/color. The two primitive costs
are the actual measurement CM44 and actual uncut matrix A45. Their unchanged
reserve and coefficient scale give globally smooth weighted H and every joint
jet bound. This supplies exact joint periodization and the unchanged background
quadrature source (`app:ch_waves:eq:background-quadrature`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

publish_original_weighted_background_budget
publish_original_weighted_background_profiles
end
