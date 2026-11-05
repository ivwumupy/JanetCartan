module
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceIdentityTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
identify_original_complete_native_source 0
identify_original_complete_native_source 1
identify_original_complete_native_source 2
identify_original_complete_native_source 3
open Lean Meta Elab Command
run_meta do
  for key in #[`nativeAmplitude,`source_eq_native,`germ_on_original_chart,`jets_on_original_chart] do
    let name := `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "physical source-D/native identity has nonstandard axioms: {axioms}"
    logInfo m!"actual physical source-D equals SAME native field on full source chart / {key}: {axioms}"
