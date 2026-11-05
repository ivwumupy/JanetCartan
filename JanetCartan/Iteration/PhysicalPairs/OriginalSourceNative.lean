module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeIdentity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
/-! # True source-tame physical profiles of the actual individual native field

The complete supplied source has its real Sobolev profile through s+n+2, and
only that legitimate source profile and its numeric scale inputs remain. The
actual inverse's all-order regularity and finite-order tame bounds are produced
internally by100, while all kernel/tester fields come from the one89 tuple.
The conclusion is C_s*h*R^s, not a Fourier-support envelope. A later actual
complete-forcing iteration and its fixed h-cap must supply the source inputs;
this source-parametric theorem does not by itself close exact Main.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.publishSourceProfile p fields 0
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.publishSourceProfile p fields 1
run_meta do
  for key in #[`profile_statement,`source_cNorm_profile] do
    let name := `JanetCartan.PhysicalPairs.OriginalSourceNative ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual source-tame physical profile has nonstandard axioms: {axioms}"
    logInfo m!"checked same actual source-only physical C_s*h*R^s profile {key}: {axioms}"
