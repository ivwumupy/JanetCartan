module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.NormalizedBounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Assembly

/-!
# Normalized external jets for annular source integration

Source: `app:ch_response:lem:energy-carrier-jets`, preserving the separate
scales in `app:ch_response:eq:direct-envelope-profile`.

`annularExternalJet` differentiates the actual oscillating vector amplitude
with external variable `(c,x)`. The original phase, full amplitude, selector,
physical frequency and carrier scale remain fixed under carrier-parameter
differentiation. Both physical and demodulated observations are included;
the latter retain the output phase before every external derivative.

`exists_originalAnnularExternalJet_profile` assembles the original two-time
phase and symbol profiles, both physical masks, beta, the selector and the
original supported envelope Sobolev profiles. For external order `j` and
source order `k`, it bounds the literal normalized jet by
`D(j,k) * (A₀ * (λ + ‖ξ‖)^j * K^(n+1+j)) * K^k`.
The constants precede all variable data; only envelope parameter orders
through `j` occur. The fixed exponents are `(0,0,n+1+j,j)` for the separate
`λ,L,K,λ+‖ξ‖` factors. The original window `1 ≤ L ≤ K ≤ λ^(1-ν)` remains.

The endpoint covers both orientations and both observations, with global
source smoothness and the same support for every source derivative. Phase
and symbol regularity is needed only on the original supported charts where
beta is nonzero. Literal kernel identities and selector/beta zero identities
hold at every physical frequency, including the shoulders and unbounded tail.
The consuming source integration and kernel estimates belong to the parent.
-/
