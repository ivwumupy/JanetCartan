module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareFamily

/-! # The actual original scalar46 bare kernel at every physical carrier node

`OriginalBareFamily.at_point` uses the before-history maximum and uniform
budget, not a supplied single-row operator or a successful sample.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
instantiate_original_native36_at_scalar46
