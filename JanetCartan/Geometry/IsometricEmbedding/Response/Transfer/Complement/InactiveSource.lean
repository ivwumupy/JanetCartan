module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Precision

/-!
# Inactive source Fourier factors

The inactive-source sentence of
`app:ch_response:thm:response-literal-transfer`.

`BoundedMask.fourierMultiplier` is the actual Euclidean L² multiplier with
symbol evaluated at the physical covector `η = 2πξ`. `carrierSource` is the
original compactly supported modulated envelope, with its L² membership and
Fourier representative proved. `localized_carrierSource_sub_identity`
retains the exact cutoff order and sign for `A₊-I`.

`masked_carrierSource_arbitrary_precision` proves arbitrary `ρ⁻Q` decay and
membership in the existing vector Fourier Sobolev spaces from the original
all-order envelope Sobolev profile. `EnvelopeJets` derives its pointwise jets
with the fixed loss `K^(d+1)`. `Sobolev` transfers the full-gap kernel estimate
to the actual multiplier. The existing scale inequality absorbs the fixed
loss, with the integration order and constant chosen before the family index.
The primitive gap covers the entire nonzero mask, including bounded
frequencies and all radial/angular shoulders.

`localized_carrierSource_observations` and
`identityError_carrierSource_observations` retain the literal physical cutoff
order and give physical/demodulated consequences under a fixed polynomial
cutoff/observation cost. The latter uses the gap on `1-m`, not on the active
mask. The masks, support plateaus, phase geometry/grades, original envelope
profile and fixed polynomial observation costs remain supplied inputs of
`jc-response-complement`. No arbitrary-accuracy premise is supplied. Parameter
labels can be included uniformly; parameter derivative identities are not
asserted. This does not complete the full graph transfer theorem.
-/
