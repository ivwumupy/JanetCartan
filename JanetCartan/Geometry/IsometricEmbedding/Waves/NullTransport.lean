module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualGaps

/-!
# Null transport: fixed-minor construction and scalar reduction

Checked components of `app:ch_waves:thm:leading`:

* nonvanishing left/right nullvectors from a fixed nonzero adjugate entry;
* the adjugate factorization, proved from the characteristic equation;
* smooth dependence of the selected nullvectors on the matrix entries;
* the exact scalar reduction for the reduced operator with Christoffel terms;
* identification of the principal field with the determinant gradient times the
  fixed minor, and its quantitative time denominator gap;
* a finite fixed-minor refinement of the actual constructed carrier, with the
  adapted time gap derived from primitive frame closeness on a larger parameter
  buffer, preserving the same charts and section normal.

`NullTransport.ActualAmplitude` additionally constructs the adapted flow and
prescribed positive null amplitude for the literal projected stress, with a
finite refinement covering the original closed carrier cube and a uniform
positive scalar lower bound. Its final theorem
`exists_finite_projected_tame_positive_amplitudes` also discharges the joint
scalar/vector tame estimate, with fixed reserve `13`, primitive `C¹²`
immersion / `C⁵` initial-data budgets, and fixed compact working sets covering
a common closed physical/carrier cylinder. All constants precede the immersion
and prescribed initial scalar. Ambient reconstruction remains with
`Waves.Leading`.

The actual construction is a separate import because the independent
`NormalizedCoefficients` leaf imports this algebraic module.
-/
