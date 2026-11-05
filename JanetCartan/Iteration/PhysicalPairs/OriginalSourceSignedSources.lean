module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedSourcesTemplate
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
/-! Complete measured plus/minus source tensors for the actual ψ-Schwartz
waves equal those from the SAME unobserved COMPLETE corrected waves. Here
raw/unobserved does NOT mean before the response correction B. The existing
χsrc and exactly one χ₂ are retained, including all doubled-plus diagonals.
This proves equality of the measured tensors, not global equality of uncut
sources or an already-closed quantitative signed correction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_original_measured_signed_sources 0
publish_original_measured_signed_sources 1
publish_original_measured_signed_sources 2
open Lean Meta Elab Command
run_meta do
  for key in #[`measuredPlus,`measuredMinus,`measured_sources_eq] do
    let name := `JanetCartan.PhysicalPairs.OriginalSourceSignedSources ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual complete measured signed source has nonstandard axioms: {axioms}"
    logInfo m!"SAME original χ₂/χsrc, complete measured signed source {key}: {axioms}"
