module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.PhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Integration

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.KernelProfiles

/-!
# Source kernels of the actual annular complement

`exists_originalAnnularSourceKernel_profile` proves the literal mixed kernel
bounds of `app:ch_response:lem:energy-carrier-jets` from original two-time
phase/symbol profiles, both masks, beta, the fixed normalized selector, and
supported envelope Sobolev profiles. The geometric inputs are the positive
carrier-gradient bounds and the actual supported elapsed radial comparison.

For source dimension `n` and fixed external order `j`, the estimate is
`C(j,N) * A₀ * (λ + ‖ξ‖)^j * K^(n+1+j) * (K/(λ + ‖ξ‖))^N`.
The losses `(0,0,n+1+j,j)` are fixed before `N`; constants precede all variable
scales, frequencies, carriers, and envelope data. The separate window
`1 ≤ L ≤ K ≤ λ^(1-ν)`, with fixed `0 < ν < 1`, is preserved.

Both orientations and both physical/demodulated observations use the literal
elapsed graph and physical Fourier normalization. Every demodulator derivative
is retained. Bounds hold at every frequency and output point, including
selector shoulders, bounded frequencies, and the unbounded tail.

`elapsedAnnularSourceKernelObservation_regularity` supplies smoothness,
frequency measurability, derivative interchange and fixed compact output
support from the original supported phase chart. `JetIdentity` identifies
its differentiated integrand with the actual normalized external jet and
also proves interchange from local source/output neighborhoods.

The independent frequency-integration and Sobolev deduction, and the final
compatible-phase/sector instantiation of the original profiles and radial
comparison, belong to the parent annular-complement construction.
-/
