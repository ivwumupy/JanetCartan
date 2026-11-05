module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.BaselineBridge
/-! The exact original unscaled raw baseline differential. The bridge supplies
its native derivative and the proved field/amplitude identifications; the
source admission is the original outer-weight admission (main:eq:primary-strain).
No inner angular condition or baseline rescaling is introduced. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual.baseline_factor
