module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.Bounds

/-!
# Rectangular derivative trade for the continuum transport adjoint

This module proves the literal identities in
`app:ch_background:eq:bg-derivative-trade`: the positive transverse gap makes
`Aᵀ A` invertible, `L = (Aᵀ A)⁻¹ Aᵀ` is a left inverse, `d_x Φ = Aη`,
`η = L d_x Φ`, and `∂_z Φ = (D_z Y)L d_x Φ`. The carrier derivative retains
`Dζ`. Smoothness follows from the actual phase and carrier. The rational
coefficient estimates are uniform one-high estimates on fixed chart balls.

`exists_cNorm_transversePhaseCoefficients_le_primitives` bounds the joint Cᵏ
norms of both `L` and `V` by one additive primitive Cᵏ⁺³ budget for `S, ζ`.
Its only low-norm hypotheses are primitive C³ bounds. The zero-order primitive
estimate discharges the rational inverse's low matrix-range assumptions; the
fixed reserve is three, independent of `k`.

All results are conditional deductions. The consumer
`jc-continuum-initial-adjoint` must instantiate the smooth Hamilton phase,
smooth carrier, quantitative transverse gap and primitive chart budgets from
`jc-hamilton-phase`, `jc-full-phase-charts`, `jc-leading-wave` and
`jc-normal-inverse-coefficients`. This module proves no unconditional Hamilton
construction or adjoint mapping theorem, and makes no measure identification.
-/
