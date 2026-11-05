module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowConic.Construction

/-!
# The actual supported conic carrier on the transport-flow neighborhood

`FlowConic.exists_actual_supported_carrier_in_open_of_primitive_controls`
places the entire coefficient domain inside any prescribed open neighborhood
of the selected incidence center, with both radii and all thresholds chosen
before the current immersion. It applies the supported-shell global carrier
constructor to the same Hamilton phase, masks, product measure, quadratures,
regularization limits, literal adjoint and reflected normal.

The remaining primitive inputs are exactly those supplied by
`CanonicalCarrier.exists_actual_canonical_primitive_controls` on its open
product neighborhood. Actual primitive/history instantiation and finite-family
assembly remain with the continuum-row parent (`app:ch_background:eq:bg-Psi`,
`bg-jacobian`, `bg-mixed-input`, and `bg-T`).
-/
