module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionCoefficients
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

/-!
# Current-stage threshold for the actual finite Picard precision

The exact common-D_N coefficient and all static profiles come from the
coefficient leaf. rho=omega is a legitimate weakening of the original
transport rate, and the full Cρ^N remains in the precision constant.
Sprecision is chosen BEFORE R0/history/target and reached at the CURRENT
stage scale. This does not alter the dimension-only initial threshold,
the source cutoff, sample, or inverse (app:ch_mean_pairs:prop:mean-iteration).
-/
define_original_full_picard_precision 2
define_original_full_picard_precision 3
define_original_full_picard_precision 4

#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.exists_precision_threshold
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.Sprecision
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.Sprecision_spec
