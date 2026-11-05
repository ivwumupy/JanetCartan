module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.Angular
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceForward
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceForwardTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceForwardTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
/-! The exact observed raw angular differential on the SAME original
unweighted adjoint input. Its prefix and source producers are supplied
internally; no additional equality or success hypothesis remains
(main:eq:primary-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
derive_original_raw_source_from_prefix 2

run_meta Lean.addDocStringCore `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.observed_raw_angular_eq_source "The observed differential of the SAME original raw angular wave equals its full raw source field on the original source chart. The original prefixed forward identity and unweighted-adjoint grouped-source identity are supplied internally, with no additional source, residual or inverse success premise (main:eq:primary-strain, app:ch_regular:eq:source-tail)."

#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.raw_angular_smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.observed_raw_angular_eq_source
