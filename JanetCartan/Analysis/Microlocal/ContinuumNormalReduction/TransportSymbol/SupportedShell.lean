module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.ConicBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.GlobalNormBounds

/-!
# Transport symbol estimates localized to the original mask support

The supported variants preserve the global homogeneous, high-cutoff and
uniformly regularized conclusions, including genuine initial multipliers.
Only shell containment is localized: for `x ∈ X` and `v ∈ S`, membership in
`closure (augmentedTransportGradient Y '' Z)` implies membership in the fixed
closed output ball. Primitive mask support proves all density jets vanish
outside this closure. No transformed-density, derivative-support or operator
estimate is an input.

All inverse/Jacobian estimates and frequency deductions reuse the existing
producers. Constants precede the varying fields, the common high norm and the
regularization radius, with coefficient order `s`, geometry order `s+2` and
fixed low geometry order three. The original spectator measure is unchanged.

The consumer is `jc-carrier-supported-shell-construction`. These conditional
bounds do not instantiate the actual geometry; that remains the obligation of
`jc-continuum-canonical-conic-inputs`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-mixed-input`, `app:ch_background:eq:bg-symbol`, and
`app:ch_background:prop:bg-frame`, Step 1.
-/
