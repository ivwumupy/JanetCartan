module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual unweighted Fourier mass on the original supplied-source wave

The sole sampled primitive tuple, same global inverse and unchanged physical
input/detector supply all analytic fields. The source is arbitrary smooth DATA.
Its H^(n+1) norm is the only right-hand source quantity. The final Picard
Cmass(N)*h statement is obtained by the genuine full-source profile; no
background-only iterate or successful mass premise is introduced
(`main:eq:primary-fixed-scales`, `app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
open Lean Meta Elab Command
run_elab do
  let payload ← JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication.sourcePayloads
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication.publish 0 payload p fields
run_elab do
  let payload ← JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication.sourcePayloads
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields =>
    JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication.publish 1 payload p fields
end
