module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds.FiniteCover

/-!
# Quantitative normalized-symbol inputs for the actual carrier menu

Step 1 of `app:ch_seed:prop:seed-actual-menu`: the literal normalized determinant
has one-high bounds of every joint finite order, with reserve zero from the
frame and reserve two from the immersion. The phase input at order `r+1`
therefore costs exactly `r+3` immersion derivatives, independently of `r`.
All frame-symbol estimates use the shared `ActualCarriers.normalizedSymbol`
definition. This is definitionally the scalar field of
`ActualCarriers.normalizedHomogeneousSymbol` from `ActualCarriers.NormalizedSymbol`;
no identification premise is needed when applying the phase construction.

`NormalizedSymbolBounds.exists_cube_symbol_C3_C6_comparison_radius` supplies
the two low-order neighborhoods used by `HamiltonPhase.FamilyConstruction`.
`NormalizedSymbolBounds.exists_symbol_comparison_radius_finiteCover` supplies
the arbitrary finite-order comparison on buffered annular covers.

These are conditional deductions. The actual carrier and coefficient-scale
owners must supply the smooth projected frame, primitive low bounds and frame
closeness, the fixed annular cover inside the construction domain, and the
primitive loss-two frame estimate. No Hamilton flow or phase estimate is assumed.
The frame regularity, low bounds and loss-two estimate belong to
`jc-projected-stress-frame`; primitive frame closeness belongs to
`jc-deduce-carrier-pencil-continuity`. Inverse norm powers are handled here by
their proved smoothness on the nonzero covector range and the existing tame
composition theorem, so no unproved inverse-jet estimate is an input.
`jc-actual-carriers` and `jc-current-coefficient-scale` must instantiate these
hypotheses and choose the buffered cover for their actual construction.
-/
