module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Assembly

/-!
# Frozen spectral bounds on the supplied initialized row

`RetainedFrozen.retained_incidence_spectral_bounds` proves continuity, uniform
boundedness, positive semidefiniteness and a positive high-frequency matrix gap
for the ideal image plus the finite reflected carrier sum on the supplied
`IncidenceCenter D` family (`app:ch_background:prop:bg-frame`, Step 2).

The primitive outer geometry is the exact output of
`UniformConic.exists_actual_refined_supported_geometry_in_open_before_geometry`,
used by `UniformConic.exists_actual_supported_carrier_in_open_before_geometry_of_primitive_controls`
and retained on the selected row by `jc-retained-frozen-unit-realization`.
Its outer `6*a ≤ r` implies the weaker outer radius bound used here;
its inner radius condition remains exactly `a' ≤ r'`.

The inner angular mask and spectator radius and the distinct outer inverse
radii are preserved. The original roots and cover are reused. The proof
constructs positive literal weights from the selected null columns and the
actual normal formula, then applies compact-sphere detection. The parent
`jc-continuum-normal` retains instantiation of primitive local geometry,
seed/covector matching, and the selected full-modulation inputs on its SAME
initialized row, followed by Fourier-energy identification and operator
coercivity. No unconditional operator existence theorem is asserted here.
-/
