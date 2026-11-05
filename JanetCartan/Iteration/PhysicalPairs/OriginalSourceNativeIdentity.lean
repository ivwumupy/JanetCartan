module
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public meta import JanetCartan.Iteration.PhysicalPairs.OriginalSourceNativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
/-! # The actual canonical source derivative is the whole native source field

Use89's one checked tuple, the same real A, complex An, full Gprefix, prefix
mask and global current Q0. Source, torus point and original sample are DATA;
there is no source profile, wave estimate, or alternate factory in the identity.
Consumer: the literal physical angular-amplitude join for `main:prop:pairs`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.publishIdentity p fields 0
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalPairs.OriginalSourceNativeTemplate.publishIdentity p fields 1
run_meta do
  for key in #[`identity_statement,`canonical_derivative_eq_native] do
    let name := `JanetCartan.PhysicalPairs.OriginalSourceNative ++ key
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual source-native identity has nonstandard axioms: {axioms}"
    logInfo m!"checked same original canonical/native identity {key}: {axioms}"
