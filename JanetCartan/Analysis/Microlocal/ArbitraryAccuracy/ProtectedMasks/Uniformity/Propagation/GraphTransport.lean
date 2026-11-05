module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.InitializedProtection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.Construction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.RootConstruction

/-!
# Quantitative transport for protected comparison graphs

Uniform comparison estimates for `app:ch_regular:thm:no-return` and the
protected finite-chain paragraph of `app:ch_regular:lem:finite-chain`.

The actual-relation theorem preserves the original masks, both orientations,
all intermediate points, and the original elapsed bound. `Construction` retains
the comparison derivative bound through the entire initialized no-return
construction, on the same charts, geometry, rectangles and weights. The field
estimate comes from the literal coefficient jets on a fixed annulus.
`RootConstruction` instantiates the root-side hypotheses on the literal conic
root producer, retaining its original flow and buffers.

The consumer retains finite root selection, source coverage, the conversion to
closed shoulders, and the finite-depth induction. These estimates alone do not
assert that final containment or the paper's unconditional existence theorem.
-/
