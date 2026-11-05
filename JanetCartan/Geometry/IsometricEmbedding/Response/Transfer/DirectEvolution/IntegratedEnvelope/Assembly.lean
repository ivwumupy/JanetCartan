module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Forward
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Adjoint

/-!
# Full elapsed-envelope profiles for the same physical factors

`Assembly.fullElapsedEnvelope_hasEnvelopeProfile_of_primitive_jets` and
`Assembly.fullElapsedAdjointEnvelope_hasEnvelopeProfile_of_primitive_jets`
instantiate both the annular and complementary primitive producers. The exact
complement identity identifies the original uncut elapsed integral in each
orientation. The resulting `HasEnvelopeProfile` has amplitude
`lam^order * A₀ * K^ps.length`, hence no extra power of `K` at spatial order `s`.
In particular, orders `0` and `-1` retain their original frequency gains.

The ordered-derivative bridge proves the addition identity from the original
fixed-time annular regularity and primitive local domination. Every parameter
derivative acts at fixed frequency and fixed physical operator. Tail precision
`-order` and `K ≥ 1` suffice; neither a transferred bound nor a full-envelope
bound is assumed.

Actual uniform sector charts, compatible critical geometry, primitive symbol
and original-datum profiles, and the original graph regularizations remain
explicit inputs from their designated constructions. These results prove the
direct-envelope deduction, not the unconditional sector, inverse or embedding.
Sources: `app:ch_response:eq:direct-envelope-profile`,
`app:ch_response:eq:fixed-factor-transfer`, and
`app:ch_response:eq:response-graded-reduced`.
-/
