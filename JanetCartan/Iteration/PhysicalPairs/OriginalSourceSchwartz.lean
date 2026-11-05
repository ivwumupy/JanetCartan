module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSchwartzSmooth
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSchwartzTemplate
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
/-! # Actual complete-source Schwartz representatives on the original chart

These are the existing observation ψ times the unweighted positive baseline
PLUS the entire source-data angular field. The raw field is unchanged on the
whole original source chart. The actual final primary still has its original
aggregate Dsmooth cutoff; its identity is a separate consumer, not a claim
that these representatives equal the raw field everywhere.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
publish_original_source_schwartz 2
publish_original_source_schwartz 3
publish_original_source_schwartz 4
publish_original_source_schwartz 5
open Lean Meta Elab Command
run_meta do
  for key in #[`wave,`wave_apply,`germ_statement,`germ_on_original_chart] do
    let name := `JanetCartan.PhysicalPairs.OriginalSourceSchwartz ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual source Schwartz representative has nonstandard axioms: {axioms}"
    logInfo m!"same actual source/observation Schwartz representative {key}: {axioms}"
