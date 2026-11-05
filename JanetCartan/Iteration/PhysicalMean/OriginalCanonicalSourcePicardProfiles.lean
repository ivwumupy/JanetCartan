module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalPicardApplication

/-!
# Finite profiles of the same original selected Picard source

The profile and its finite-step dependence are deduced, not assumed.
The three named primitive producer inequalities remain explicit until
88/102/99 are applied. This module alone is not an actual source estimate
or a completion of `main:prop:mean`.
-/

set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
construct_actual_canonical_picard_profile
