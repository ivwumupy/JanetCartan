module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.PhysicalDerivative

/-!
# Graded bounds for the same ambient reconstruction

`completedVariationComplex_displacement_graded` and
`completedVariationComplex_physicalDerivative_graded` construct actual Euclidean
L² representatives of the demodulated displacement and physical differential of
the same completed variation. They prove the bounds in
`app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative` for real `0 ≤ s ≤ k`.

All coefficient products are estimated from primitive finite local budgets as
in `app:ch_response:eq:response-reconstruction-grading`. Constants are explicit
and independent of `A`, `L`, `K`, and `ρ`. Derivative envelopes are estimated from
the root Hilbert Sobolev profiles, retaining the Fourier factors `2π`.
The source uses all tensor coordinates and both complex quadratures. The
observation cutoff remains outside the physical derivative, including `iρ dφ`.

These are conditional analytic deductions. The parent must supply the reduced
and source root profiles, primitive local coefficient budgets, and the finite
classical L² jets with their weak derivative recursion. The separate smooth-jet
producer supplies those representatives; no ambient bound is an input here.
-/
