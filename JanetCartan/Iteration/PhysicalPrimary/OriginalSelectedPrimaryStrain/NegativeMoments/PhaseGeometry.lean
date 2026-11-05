module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Phase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.NegativeMomentsTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! # Actual source geometry of the original primary representative

The same representative and protected compact give the positive gradient
lower bound and all phase jets at the current scale over every admitted
label. This input to negative moments is independent of the source identity
(`app:ch_regular:eq:inverse-remainder`, `main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

price_actual_primary_negative_source 3

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.source_geometry
