module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalWorkingProfilesApplication

/-!
# Actual positive coefficient profiles on the one original sampling radius

`OriginalRetained.on_original_sampling_radius` retains the original positive51
prefix, the SAME coefficient/phase/reconstruction functions and all before-history
budgets. The selected row proves its own original root admission. The doubled
working ball is contained in the phase domain, the four coefficients are smooth
on its open ball, and all five profiles and free-covector jets hold on its closed
inner ball. The radius is literally `originalSamplingRadius`, not a new choice.

The actual positive-density profile and full corrected response still belong to
their parent constructions. This is not the completed normal comparison.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

apply_profiles_on_original_working_radius
