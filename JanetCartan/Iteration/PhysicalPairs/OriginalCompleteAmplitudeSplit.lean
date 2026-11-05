module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeSplitTemplate
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
/-! The actual complete Schwartz amplitude is exactly the actual unscaled
physical baseline plus the SAME canonical complete source derivative on the
entire source chart. The equality is a germ, hence preserves every jet. The
quantitative baseline and actual complete-forcing/h-cap instantiations are
separate obligations, not assumptions hidden in this exact split. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
split_original_complete_amplitude 0
split_original_complete_amplitude 1
split_original_complete_amplitude 2
split_original_complete_amplitude 3
split_original_complete_amplitude 4
open Lean Meta Elab Command
run_meta do
  for key in #[`baselineAmplitude,`sourceAmplitude,`amplitude_eq_base_add_source,
      `germ_on_original_chart,`jets_on_original_chart] do
    let name := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual complete amplitude split has nonstandard axioms: {axioms}"
    logInfo m!"actual unscaled baseline + SAME canonical whole source, full-chart amplitude {key}: {axioms}"
