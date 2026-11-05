module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Carriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Domains
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.AmplitudeSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Assembly
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.ResidualCarriers

/-!
# Geometry on the retained selected elapsed carriers

The carrier and lower-time conclusions here use the same endpoint output,
chart input, and doubled physical multiplier as the full direct residual.
`exists_selected_elapsed_noncomparable_geometry` constructs the physical
domains and carriers and proves the uniform covector comparison under the
explicit supported-phase germ agreement. `exists_selected_direct_residual_carriers`
assembles compact comparable support, the original source buffer and output
slab, and bounded radial dilation into the original amplitude band for every
nonzero jet of the literal common-mask direct residual. All constants precede
accuracy, coefficients and scales. Auxiliary phase construction and analytic
profile transfer remain with the parent elapsed-grade construction.

Consumer: `ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
Sources: `app:ch_regular:eq:high-phase`, `app:ch_regular:eq:high-amplitude`,
`app:ch_regular:eq:chain-tail`, and
`app:ch_regular_base:eq:energy-complete-residual`.
-/
