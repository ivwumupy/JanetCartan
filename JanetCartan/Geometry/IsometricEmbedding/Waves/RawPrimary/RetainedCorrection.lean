module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.Nonvanishing
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.Finite

/-!
# Correction estimates for the initializer's retained witnesses

For `app:ch_waves:eq:primary-algebraic-correction` and
`app:ch_waves:eq:WKB-grading`, the retained Hamilton geometry proves
full-phase transversality and selected-denominator nonvanishing. The retained
quantitative null-column bound gives a compact range for the existing
orthogonal correction, preserving its reserve fourteen and all flow witnesses.

`exists_retained_cell_correction_bounds` consumes the original working-ball
containments retained by the finite and history leading producers. It applies
to already selected witnesses, including the common initializer's family.
`exists_finite_retained_corrected_family_before_geometry` applies it to the
actual finite producer and retains every original conclusion. Coverage uses
radius `σ`; correction estimates hold on the larger radius `2 * σ` balls.
No covering cell is shrunk, and constants precede the varying immersion,
initial scalar, frequency and history scale. The raw-primary parent retains
prepared-scalar and final initialized-history instantiation.
-/
