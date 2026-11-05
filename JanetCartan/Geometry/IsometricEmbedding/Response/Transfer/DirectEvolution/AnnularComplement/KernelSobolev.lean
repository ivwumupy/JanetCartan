module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.Assembly

/-!
# Full annular kernel integration and vector Sobolev precision

`annularKernel_sobolev_realization` proves the independent implication used by
the same-operator annular-complement assembly in
`app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`.

It derives full-frequency integrability, joint differentiation under the
integral, actual parameter derivatives in L², and arbitrary precision in every
real vector Fourier Sobolev order. Its inputs are ordinary vector kernels,
joint smoothness on an open parameter box, frequency measurability, one compact
physical output support, and the stated annular profiles of actual joint jets
on unit directions. All coefficient/envelope losses are fixed before accuracy.

Apply it separately to the literal physical and demodulated kernels, whose
profiles remain the responsibility of `AnnularComplement.SourceBounds`.
Identification with the exact uncut graph difference remains with the parent
construction using `SupportedIdentity` and `ElapsedIdentity`.
-/
