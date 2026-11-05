module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfilesApplication

/-!
# Original corrected-amplitude input for the Hermitian profile

Retain the SAME matrix amplitude occurring in `OriginalMeasuredFamily.Row.kernel`
and its before-history nonnegative all-order budget. The global joint bounds
are deduced from the existing five raw profiles and the SAME full-response jet
input of `OriginalMeasuredCurrent.mean_on_full_response`, using only the
support of the existing coefficient cutoff outside the original working ball.

This is not yet the full measured Hermitian source theorem. Actual response
profile instantiation on the whole working compact, carrier pullback and the
unchanged full positive physical weighting are separate outstanding obligations.
No generic desired-profile hypothesis is presented as an actual construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

retain_original_corrected_amplitude_jets 0
retain_original_corrected_amplitude_jets 4
retain_original_corrected_amplitude_jets 1
retain_original_corrected_amplitude_jets 2
retain_original_corrected_amplitude_jets 3
