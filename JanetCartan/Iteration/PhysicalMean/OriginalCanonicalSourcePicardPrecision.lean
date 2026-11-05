module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalPicardPrecisionApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication

/-!
# Same original operators with a forcing DATA parameter

The finite run, residual and next-difference identity accept g as DATA. They
do not assert that99's quadrature forcing is the full paper source. The finite,
middle and C1 estimates remain conditional on the genuine primitive bounds;
the parent must construct the complete source and prove its forcing profile.
The frozen background-only run and input ABI are not redefined.
-/

set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
construct_original_fixed_forcing_source
construct_original_fixed_forcing_middle_precision
construct_original_fixed_forcing_cnorm_precision
