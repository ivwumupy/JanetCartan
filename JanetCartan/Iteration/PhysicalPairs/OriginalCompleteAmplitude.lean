module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
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
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights
/-! Actual complete Schwartz derivative amplitudes use the original carrier
phase and preserve every raw complete-wave jet on the full source chart.
These are exact identities, not quantitative profiles for the oscillatory
wave or a claimed completion of the signed-pair bound. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_original_complete_amplitude 0
publish_original_complete_amplitude 1
publish_original_complete_amplitude 2
publish_original_complete_amplitude 3
publish_original_complete_amplitude 4
open Lean Meta Elab Command
run_meta do
  for key in #[`phase,`rawAmplitude,`amplitude,`germ_on_original_chart,`jets_on_original_chart] do
    let name := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual complete amplitude has nonstandard axioms: {axioms}"
    logInfo m!"same actual carrier, complete amplitude and original source-chart jets {key}: {axioms}"
