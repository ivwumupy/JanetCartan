module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Sobolev
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Primitive

/-!
# Graph, inverse-graph, and diagonal factor localization

`exists_graph_factor_sobolev_bound_of_primitive_grades` instantiates the
physical-shell estimates at every order through `m` and constructs one
identified operator with all the bounds in `app:ch_regular:eq:chain-tail`.
Its constants precede the varying phases and scales; the accuracy-dependent
constant is separate from the fixed powers of `ρ` and `L`.

The imported stationary and buffered-localizer results retain both base
equations, full source shoulders, and the complementary symbol's identity
term. The physical cutoff families include arbitrarily small graph frequencies.
Smooth phase extensions are constructed only on each compact frequency piece
and removed from the exported physical actions. Both orientations and every
real full-symbol order use the same theorem; the weighted inverse and diagonal
specializations use the exact identities in `Graph.Basic` and `Graph.Phase`.
-/
