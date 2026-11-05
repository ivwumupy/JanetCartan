module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveRaw
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceApplication
public import JanetCartan.Iteration.PhysicalPrimary.OriginalStressClassTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalStressTemplate

/-! # The original smooth forcing and its literal tensor quadratures
Cache the native Source53 class and the physical carrier realization before
identifying them on the open plateau. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
identify_original_source53_stress_class
instantiate_original_physical_stress_part 0
instantiate_original_physical_stress_part 1
