module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.Construction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction

/-!
# Evolution witnesses retained by the actual amplitude constructors

`exists_uniform_pencilAmplitudes_with_retained_evolution` and
`exists_uniform_supported_conic_pencilAmplitudes_with_retained_evolution` in
`JanetCartan.RegularSector.Characteristic.UniformAmplitudes` retain the primitive
evolution of their actual coefficient root, Hamilton flow and inverse chart.
The existing public endpoints are projections of these stronger constructions.

The positive `evolutionTime` and `rootCost`, together with the original
`phaseCost`, are chosen before masks, varying coefficients and jet orders.
The flow retains radii `L` and `L / 2`; its compact jet domain is exactly
`closedBall z (L / 4) ×ˢ Icc (-evolutionTime / 4) (evolutionTime / 4)`.
The state/projection and inverse/phase jet domains have the original radii
`a` and `b`. Root estimates have coefficient shift zero; the joint geometry
estimate has shift one and uses the original `phaseCost`.

For every point of the same chart target, every time in the unoriented closed
segment from source time to output time retains domain inclusion, the ambient
ODE, range in `closedBall z L`, and the clock identity. Both constructors also
retain `Φ (w, 0) = w` on `ball z a`. The conic endpoint keeps the same masks,
literal supported matrices, smooth phase `G`, cancellation, upper endpoint
and all original amplitude budgets.

Consumers: `ResponseTransfer.RetainedFactors.exists_retained_conic_critical_geometry`
and `CompatibleResponse.elapsedModulatedPhase_critical_value`, for
`app:ch_response:eq:response-exact-phase` and
`app:ch_response:eq:direct-envelope-profile` in `paper.tex`, and
`app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
Primary-domain containment, zero critical value, uniform critical geometry and
the final response construction remain obligations of those consumers.
-/
