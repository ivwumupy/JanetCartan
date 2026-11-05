module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensity
public import JanetCartan.Iteration.PhysicalGeometry.Retained
public meta import JanetCartan.Iteration.PhysicalBackground.NativeCoefficientProfilesTemplate

/-!
# Native coefficient profiles for the actual positive background

Consumer: the literal cutoff-one, factor-two measured-source high estimate of
`app:ch_background:prop:bg-current`. This uses the same generic coefficient
producer as the original regular operator, on the native first18 reference and
same source dilation, qext, b/R, band and reserve data.

The prefix is native raw21 plus sigma and its normal-current-inverse interval,
then the eight existing coefficient-producer numerical inputs. S/AQ/AB are
selected before all histories. No regular-sector cap implication is asserted.
The parent must verify all shared producer arguments before identifying these
constants with the regular operator packet, and explicitly include S in its
prehistory threshold maximum. Raw projectedStress is recovered by the existing
zero-loss affine-extension cNorm identity on the original measurement buffer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000

@[expose] public noncomputable section

realize_native_coefficient_profiles
