module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventBudget
public import JanetCartan.Iteration.PhysicalBackground.NativeDensityProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalBackground.NativeDensityProfilesTemplate

/-!
# The genuine high native profile on the bare-admitting sampler data

Fix the unscaled `initialC` and size-σ sampler bound before any response budget,
then reach the actual native density and operator thresholds on the same finite
history. No event, even conditional, is required to obtain either the full
source reserve or the sampler's lower initial-profile reserve
(`app:ch_background:prop:bg-current`, `new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

choose_original_native_initial_threshold 0
choose_original_native_initial_threshold 1
choose_original_native_initial_threshold 2
choose_original_native_initial_threshold 3
choose_original_native_initial_threshold 4
choose_original_native_initial_threshold 5
choose_original_native_initial_threshold 6
choose_original_native_initial_threshold 7
choose_original_native_initial_threshold 8
prove_original_native_initial_profile 0
prove_original_native_initial_profile 1
