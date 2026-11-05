module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalStress
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalObservationTemplate

/-! # Native uncut fixed-solver solution and its classical parameter classes
The solver, full complex inverse, original stress split, and global Fourier
classes here are all evaluated at the same physical history and rate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

construct_original_physical_observation_part 0
construct_original_physical_observation_part 1
