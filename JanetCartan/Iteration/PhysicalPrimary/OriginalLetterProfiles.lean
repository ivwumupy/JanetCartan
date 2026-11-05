module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterCurrent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPdoProfiles
public import JanetCartan.Analysis.Microlocal.SelectedResidualInputs.CollarDomain
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterProfilesTemplate

/-!
# Actual all-history coefficient and phase fields of the native letter steps

Apply the original current, full reduced coefficients, same physical phase,
source-only masks and retained native symbols. This specializes every analytic
operator/phase field of residual53 and solver50; the remaining source admission
is the primitive Fourier profile of the actual original full-strain source.
It is not a response estimate. The actual parent must still apply that source
producer and the finite-word/remainder assembly before it has a full response
bound (`app:ch_response:eq:response-graded-reduced`, `app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalLetterProfiles

apply_original_native_letter_profiles

end JanetCartan.PhysicalPrimary.OriginalLetterProfiles
