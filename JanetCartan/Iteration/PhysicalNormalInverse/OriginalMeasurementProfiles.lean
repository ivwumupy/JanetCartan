module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalMeasurementProfilesApplication

/-!
# The actual native-current common measurement budget

One Cmeasure is chosen from the original source-dilated reference and the SAME
once-capped common measurement radius, before histories, selected rows and
positive densities. `on_current` proves global smoothness and physical/joint
profiles at reserve `rStar - 2`; `at_reserve` weakens the reserve with no new
budget or measurement. The exact native current's frame supplies every
coefficient input. This is a producer application, not an assumed profile.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000
open scoped Matrix.Norms.Frobenius

cache_original_measurement_profiles
apply_original_current_measurement_profiles
