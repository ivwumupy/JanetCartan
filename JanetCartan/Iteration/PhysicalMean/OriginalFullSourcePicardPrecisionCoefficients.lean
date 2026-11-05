module
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardBudgets
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

/-!
# Exact static contraction coefficient for the original finite Picard source

Actual Cnormal=As+At with As=Cs/gamma and At=Ct/gamma. The coefficient is
EXACTLY As+At+2*c0*COMMON D_N(m0), with D_N the finite sum of P_j. These
constants precede R0/history/target/sample. They do not assert the final
residual or choose a stronger event (app:ch_mean_pairs:prop:mean-iteration).
-/
define_original_full_picard_coefficient 0
define_original_full_picard_coefficient 1
define_original_full_picard_coefficient 2
define_original_full_picard_coefficient 3
define_original_full_picard_coefficient 4
define_original_full_picard_precision 0
define_original_full_picard_precision 1

#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionSteps
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.precisionTailOrder
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.As
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.As_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.At
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.At_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.Cnormal_eq_As_add_At
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.Cρ
#print axioms JanetCartan.PhysicalMean.OriginalFullSourcePicard.Cρ_nonneg
