module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.OriginalSupport

/-!
# Actual raw-phase physical adjoint geometry

The literal current Hamilton quotient is represented on the original support
by one jointly smooth averaged-covector family. The original frozen/current
comparison constructs its transverse mixed inverse and a uniform value bound.
Primitive immersion profiles then give full physical jets with reserves
`rStar - 4` for the averaged phase and `rStar - 5` for the trade directions.

The physical isometry retains time derivatives. A single joint localization
preserves all original-support germs; the fixed-word physical jet interface
has no input-frequency or band loss. The original fine input band, including
its full dyadic ceiling, lies in that same compact after one pre-history scale
threshold. No original physical or carrier cutoff is reselected.

Consumers: `PhysicalMean.sampledAdjointMomentExpansion_realizes` and
`PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`, for
`app:ch_mean_pairs:eq:raw-adjoint-moments`.
-/
