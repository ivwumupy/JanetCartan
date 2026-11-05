module

public import JanetCartan.Iteration.PhysicalBackground.NativeAdmission
public import JanetCartan.Iteration.PhysicalBackground.NativeLeadingProfiles
import all JanetCartan.Iteration.PhysicalBackground.MeanProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.CarrierPullback
public meta import JanetCartan.Iteration.PhysicalBackground.NativeMeanProfilesTemplate

/-!
# Whole-outer-weight native current mean profiles

Consumer: the cutoff-one measured residual high profile of
`app:ch_background:prop:bg-current`. The actual protected chi and native
constant-initial carrier are retained on closedBall(5*rMeasure) times the
ENTIRE tsupport chi. The original product graph maps this compact into the
same full leading cell. Real fixed pullback and the existing weighted integral
estimate introduce no further derivative loss.

C is fixed on native original31 before history. The history profile uses
NativeAdmission39 with rSource and rSource+14<=rStar inserted before history6.
No mean/principal success premise or smaller external weight is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
open JanetCartan JanetCartan.PhysicalBackground JanetCartan.PositiveBackground
open JanetCartan.ContinuumRow JanetCartan.ContinuumRow.LeadingPrimitive
open JanetCartan.ActualCarriers JanetCartan.FrozenMenu JanetCartan.ActualCarriers.CurrentFullPhase
open JanetCartan.LeadingWave JanetCartan.LeadingWave.FullModulation
open JanetCartan.CurrentMean.PreparationTransportPrimitives

realize_native_whole_weight_mean_profiles
