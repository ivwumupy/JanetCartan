module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensity
public import JanetCartan.Iteration.PhysicalBackground.LeadingMean
import all JanetCartan.Iteration.PhysicalBackground.LeadingMean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeLeadingProfilesTemplate

/-!
# High principal profiles on the unchanged native leading cell

Consumer: the whole-external-weight mean in `app:ch_background:prop:bg-current`.
The actual selected cell supplies all leading data, scalar compatibility and
null-field smoothness. No high principal estimate is a premise. Constants and
the whole original product graph precede every history. The only extra reserve
condition is numerical: rSource+14<=rStar. The scale remains the literal
currentCoefficientScale R0 stage.

Static C/Jfull/graph getters use original31 plus the native carrier index.
History getters use the unchanged CurrentLeading.Selected all38 interface.
The profile adds rSource and its numerical certificate BEFORE history6/index.
This leaf does not shrink the external cutoff or select another leading cell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

@[expose] public noncomputable section

realize_native_leading_profiles
