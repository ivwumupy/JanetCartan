module

public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitian
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# Actual common measurement primitive on the saved native event

`CM` and `measurementS` have only the original44 prehistory inputs, before
R/history/row/color. The original saved event ALREADY dominates this measurement
threshold (`measurementS_le_eventS`, original44 plus row); the Lead can retain
that single event threshold without taking another maximum.

`joint_profile` supplies arbitrary-set profiles of the literal actual95
`OriginalBackgroundHermitian.C` pulled back by the first projection, at exactly
the sampler mean's `rawSliceParameterOrder` and `currentCoefficientScale`.
`physical_profile` and `smooth` retain the same global producer, current, radius
and budget. No analytic-success premise, new event/sample, altered reserve,
inner coefficient mask or rescaling of the positive baseline is introduced.

Consumer: `HermitianCarrierPullback.exists_weighted_local_carrier_profiles`
(`app:ch_waves:eq:background-quadrature`,
`app:ch_mean_pairs:eq:comparison-input`). This primitive alone is not Main.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

retain_actual_background_measurement 0
retain_actual_background_measurement 1
retain_actual_background_measurement 2
retain_actual_background_measurement 3
retain_actual_background_measurement 4
retain_actual_background_measurement 5
retain_actual_background_measurement 6
retain_actual_background_measurement 7
retain_actual_background_measurement 8
retain_actual_background_measurement 9
retain_actual_background_measurement 10
retain_actual_background_measurement 11
