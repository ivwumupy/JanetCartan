module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FirstMask.Costs
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.NegativeMoments.PhaseGeometry
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.NegativeMomentsTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Original primary source geometry and fixed negative-moment price

The protected compact excludes zero and the same global representative
has the original phase gradient there. These actual inputs and the fixed
derivative profiles choose the price before the source identity is applied
(`app:ch_regular:eq:inverse-remainder`, `main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

price_actual_primary_negative_source 0
price_actual_primary_negative_source 1
price_actual_primary_negative_source 2

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.CN_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.source_geometry
