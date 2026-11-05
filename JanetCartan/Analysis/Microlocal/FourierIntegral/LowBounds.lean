module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactNormal
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.VectorGraph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Symbol
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactEstimate
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Primitive

/-!
# Source-independent graph low bounds

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the actual compact
cross normal is identified with the existing vector two-position PDO after
averaged-gradient substitution and exact physical-to-cycle normalization.
`exists_compactVectorGraph_bound` derives the linear amplitude bound from
original primitive jets, with reserve `2 * (n + 1)`.

`exists_graphL2_of_primitive_inputs` constructs the unique bounded uncut graph
from original uncut primitive jets. The uniform cutoff jets are derived in
`CutoffJets`, and `PrimitiveLimit` constructs the Fatou/density extension.
The resulting graph and its literal adjoint have norm at most `C * a`, with
`C` chosen before the amplitude and its nonnegative size `a`. The theorem
proves compact-test and Schwartz realizations, strong convergence of the
actual compact graphs and their adjoints, exact right-frequency multiplier
identities, and physical source multiplication with its adjoint and norm bound.

The construction assumes no cutoff-amplitude jets, transformed normal bounds,
normal identities, limiting operators or convergence. The original chart,
linear averaged-gradient growth, buffered support geometry, normalized
Jacobian/inverse jets, and original amplitude support, jets and polynomial
domination remain conditional inputs. Their Hamilton/compatible-geometry,
inverse-coefficient and amplitude producers are listed in `LowBounds.Primitive`;
the consuming parent tasks must instantiate every input. This proves the
primitive low theorem, not the full finite calculus or final existence theorem.
-/
