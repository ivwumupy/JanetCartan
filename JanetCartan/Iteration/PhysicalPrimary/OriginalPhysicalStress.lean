module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalForcing

/-! # The admitted physical stress of the original observed inverse
The native raw strain source, real smooth admissions, actual parameter plateau,
and the same observed inverse meet here. The rate is the physical reciprocal;
the two quadratures are not independently reselected. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

instantiate_original_physical_stress_part 2
instantiate_original_physical_stress_part 3
instantiate_original_physical_stress_part 4
