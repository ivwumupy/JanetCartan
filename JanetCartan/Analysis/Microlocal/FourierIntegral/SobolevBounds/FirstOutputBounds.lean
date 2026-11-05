module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.WeakIdentities
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.PrimitiveInputs

/-!
# First output identities and primitive bounds for gain one

The gain-one paragraph after `app:ch_regular_base:eq:graph-derivative-transfer`.
The weak identities are proved from compact-frequency integration by parts and
distributional realizations of the initial and first-output kernels. The adjoint
is the supplied literal Hilbert adjoint, with original coordinates and regularizers
conjugated exactly once.

The finite joint Leibniz formulas and weighted Frobenius bounds show that one
fixed extra primitive derivative changes order minus one into order zero.
`weighted_graphFirstOutputAmplitude_of_primitive_jets` and
`weighted_adjointFirstOutputAmplitude_of_primitive_jets` take only ordinary local
smoothness and explicit weighted primitive jets. No operator estimate is assumed.

The consumer `jc-deduce-fio-strong-sobolev` must instantiate the realizations and
primitive bounds, apply its order-zero theorem, and reconstruct vector Sobolev
regularity. The present module does not assert that final Sobolev estimate.
-/
