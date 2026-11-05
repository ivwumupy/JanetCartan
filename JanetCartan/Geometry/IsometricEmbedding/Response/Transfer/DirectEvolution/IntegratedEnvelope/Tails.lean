module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Tails.Identification

/-!
# Complete complementary tails on the fixed elapsed interval

`Tails.originalAnnularComplement_elapsed_sobolev` integrates the completed
fixed-time primitive endpoint on the same physical graph, with both masks,
beta, shoulders, unbounded frequency tail and exchanged adjoint order intact.
It proves time measurability, integrability, all carrier derivative passages,
arbitrary real Sobolev precision, and the exact physical integral difference.
The identification leaf connects the result to the annular integral and its
bounded realization used by the parent envelope assembly.

The original sector/compatible-phase primitive data and the outputs of
`EvolutionIntegral.exists_elapsedGraphFamily_of_primitive_phase` must still
be instantiated by the parent for its physical family. This module does not
assert an unconditional sector construction or `HasEnvelopeProfile`.
Sources: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`.
-/
