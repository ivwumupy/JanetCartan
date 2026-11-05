module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AssemblyFromSource
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Source
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Phase
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AssemblyTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AssemblyTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
/-! The same original raw complete primary wave has, on its original source
chart, the undoubled history carrier times its unscaled raw baseline plus its
whole raw source amplitude. Every ingredient is the actual original producer;
no source, profile, residual, strain, or inverse success hypothesis is added
(main:eq:primary-strain, app:ch_regular:eq:source-tail). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

identify_original_raw_primary_factor 2

run_meta Lean.addDocStringCore `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.raw_factor_on_source_chart "The differential of the SAME original complete raw primary wave equals the undoubled historyScale^carrierExponent group-phase carrier times its unscaled raw baseline plus the same full raw source amplitude, on its original source chart. All original differential, prefix, source, plateau and regularity producers are supplied internally; no successful-construction or strain premise is added (main:eq:primary-strain, app:ch_regular:eq:source-tail)."

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.phase_eq_original_carrier
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.raw_factor_on_source_chart
