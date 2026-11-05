module

public import JanetCartan.Iteration.PhysicalRawInterpolation.Augmented

/-!
# Actual full-input interpolation for current inverse continuity

For `app:ch_background:prop:bg-adjoint`, the same original augmented input
satisfies `X_m u ≤ (card ι + 2) * (K^m * ‖u‖ + K⁻¹ * X_(m+1) u)`.
The carrier terms use the complete physical initial-variable Sobolev norm
after the original partial unitary inverse. Both periodic auxiliary inputs
are retained. The finite factor depends only on the original continuum menu.

The current-source continuity producer must establish its high-order bound
uniformly BEFORE choosing the L² tolerance. This interpolation theorem does
not replace that producer and cannot hide a history-dependent high norm.
-/
