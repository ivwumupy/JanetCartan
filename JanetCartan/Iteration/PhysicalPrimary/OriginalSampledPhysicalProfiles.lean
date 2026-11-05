module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveEnvelopeApplication
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesWhole
public import JanetCartan.Iteration.PhysicalPrimary.WeightedSynthesis
public import JanetCartan.Iteration.PhysicalMean.FixedSourceFourierMass
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights

/-!
# Sharp physical profiles on the unchanged original sampled family

The baseline atomic jets below come from the actual native scalar, raw retained
coefficients, full uncut response and original colored stage-rate margins. The
complete selected-source mass-jet proposition retains the original parent cell,
not a newly chosen sub-ball; its proof is a separate pending publication. All
constants precede the physical history and the actual event, and every original
zero angular-factor label is retained.

The frozen `selectedFinalCombinedWave` is a checked data case for the existing
background-quadrature-only source; it is NOT the final physical-step wave.
The quantitative application must use the original unweighted component input
of the complete source iterate, whose forcing also includes the leading versus
corrected mean discrepancy and the normalized physical history residual.

The uniform physical profile still requires the genuine native low Sobolev
bound for that complete source, with the published Fourier normalization, an
unscaled positive baseline, and the original zero-safe inner angular branch.
An arbitrary `WideInput`, a background-only forcing bound, or a successful output
norm premise is not a substitute. These deductions alone do not claim the
unconditional primary profile or Theorem 1.1 (`main:eq:primary-fixed-scales`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

publish_quantitative_original_uniform_cost 0
publish_quantitative_original_uniform_cost 1
publish_quantitative_original_uniform_cost 2
publish_quantitative_original_source_combined_wave
publish_quantitative_original_baseline_sharp_jets

-- This is the exact original source mass-jet proposition, not yet its proof.
-- Its actual literal Fourier-mass inequality is checked separately before release.
publish_quantitative_original_selected_mass_jets 0

end
