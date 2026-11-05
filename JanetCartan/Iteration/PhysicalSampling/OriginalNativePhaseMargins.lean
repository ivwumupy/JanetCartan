module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPhaseMargins
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativePhaseMarginsApplication

/-!
# Same-current native-map phase admission

The graph's original numerical parameters and source/threshold inequalities
remain explicit. Only the reference map is unfolded to the literal
`sourceDilation H.map σ`, which is also used by the native31 inverse/current.
Taking a common maximum threshold joins these statements with native measured
profiles; native31 alone does NOT imply the required graph margin
(`app:ch_seed:setup:seed-current`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

cache_original_native_phase_margin 0
cache_original_native_phase_margin 1
