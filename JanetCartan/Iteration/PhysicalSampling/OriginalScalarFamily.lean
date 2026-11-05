module

public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarHistory
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalScalarFamilyApplication

/-!
# Prehistory finite scalar sharp and mean budgets

These are literal finite sums of the already-retained actual scalar row
constants. Every summand is nonnegative and bounded by its common sum, including
an empty family. No row, scalar kernel, weight, current map or sample is changed
(`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

cache_original_scalar_family_bound 0
cache_original_scalar_family_bound 1
