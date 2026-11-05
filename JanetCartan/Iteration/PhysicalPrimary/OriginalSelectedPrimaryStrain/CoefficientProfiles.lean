module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Basic
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication

/-!
# Actual full primary coefficients at the history scale

`Native.Q` is the full `OriginalRegular.Current.Q` of the SAME selected weak
current. `Native.A` is exactly the existing `2J_F` coefficient. Both are
globally smooth and have ordinary all-order jets on the entire original
`OriginalSourceMasks.chart`. The cutoffs are the existing `χ₂` and `χsrc`.

`CQ = OriginalOperatorProfiles.AQ`, `CA = OriginalPrimaryStrainMaskData.Native.C`,
and the fixed compact cutoff prices `X,Y` have the prehistory native44 prefix.
All jet bounds use `historyScale R₀ growthExponent j`, after deriving the
comparison with `currentCoefficientScale` from the already reached original
operator threshold. No new analytic assumption, frequency threshold, source
cutoff or frame is selected.

Consumers: `PhysicalPairs.SampledMask.first_mask` and the negative source
moments for `main:eq:primary-strain` and `app:ch_regular:eq:source-tail` in
paper-v2. These coefficient facts alone do not prove the primary strain bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

publish_original_primary_coefficient_profiles 0
publish_original_primary_coefficient_profiles 1
publish_original_primary_coefficient_profiles 2
publish_original_primary_coefficient_profiles 3
publish_original_primary_coefficient_profiles 4
publish_original_primary_coefficient_profiles 5
publish_original_primary_coefficient_profiles 6
publish_original_primary_coefficient_profiles 7
publish_original_primary_coefficient_profiles 8
publish_original_primary_coefficient_profiles 9

end
