module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.FullCompatibility

/-!
# Partial Fourier realization of carrier data

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
`partialUnitaryInverse` is the actual unitary radian inverse Fourier
equivalence on the literal product-measure carrier L² space. Its integral
formula on compact smooth tests, both inverse identities and Plancherel are
proved. The transverse Fourier action has the exact `synthesisFactor n`
amplitude and `2π` rescaling, including in dimension zero.

The Hilbert-valued parameter Fourier operator commutes with every bounded
transverse operator. The full `initialFourier` factorization is proved and
assembled with the transverse rescaling. This gives exact norm identities
for bounded transverse operators, including the truncated frequency weights
needed by the parent initial Sobolev construction.
-/
