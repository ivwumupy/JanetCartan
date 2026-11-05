module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations.Bounds

/-!
# Compact masked direct relations and uniform covector bounds

For `app:ch_regular:lem:finite-chain`, the actual masked zero-energy relation is
the compact continuous image of its closed accepted initial-state/time carrier.
Both orientations and every intermediate segment point are retained. A finite
chart union supplies `isCompact_physicalDirectRelation`, the compactness input
of the nested proof-mask construction. The full diagonal is handled separately
by closedness and compactness over compact inputs.

The covector bounds use the actual coordinate split and primitive transverse
and root-value bounds. The common constants precede the varying roots and flows.
`rootBuffer_bounds_of_section_and_ball` connects these inputs to the section,
ball and root bounds of `UniformGeometry/RootFlow` and `Construction`.

Remaining parent obligation: select the actual finite family, its compact
initial and whole-segment buffers inside the original open root domains, and
the fixed common elapsed interval; restrict the SAME produced root and flow
continuity and bounds to those buffers. This module asserts neither compactness
of a coefficient class nor existence of masks or protection data.
-/
