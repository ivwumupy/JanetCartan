module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic.Construction

/-!
# Supported conic carriers chosen before source-dependent budgets

`UniformConic.exists_actual_supported_carrier_in_open_before_geometry_of_primitive_controls`
constructs all radii, masks, coefficient charts and a positive frame tolerance
before the geometric and primitive budgets. The prescribed open coefficient
neighborhood precedes those choices, and contains the entire coefficient domain.

The proof directly extracts the budget-independent actual chart and shell
constructions, then applies the supported global carrier constructor to the
SAME family, phase, masks, half-order amplitude and full reflected normal.
The original product measure, both quadratures, factor four, literal adjoint
and regularization limits are retained. Its exact primitive controls (including
geometry order `s + 2`) must still be instantiated by the continuum-row parent,
which also owns finite coverage and the single initialized source scale.

Sources: `app:ch_background:defn:bg-row`, `app:ch_background:eq:bg-Psi`,
`bg-jacobian`, `bg-full-complex-amplitude`, and `new:sec:order-of-choices`
(paper-v2.tex).
-/
