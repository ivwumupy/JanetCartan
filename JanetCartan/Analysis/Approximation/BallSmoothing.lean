module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Components
public import JanetCartan.Analysis.Approximation.BallSmoothing.UnitNorms

/-!
# Finite-moment smoothing on a ball

This is the actual construction in Section 6.1 of `paper-v2.tex`,
`app:ch_regular_base:lem:ball-extension`, with no assumed smoothing bounds.
It is distinct from the older dyadic Seeley extension construction.

* `exists_ballSmoothing` constructs a real linear family on smooth
  closed-ball representatives, independent of their exterior values. One
  compact subset of the prescribed open neighborhood contains all outputs.
  The output is globally smooth, all integer Sobolev jets are admitted in
  `L²`, both norms are bounded by `C r * R^r * ‖f‖C⁰`, and approximation is
  bounded by `A * (R⁻¹)^m * ‖f‖Cᵐ` for the same literal operator.
* `unitSmoothing` is exactly the fixed normalized real kernel, actual thin
  cutoff, and finite binomial sum in
  `app:ch_regular_base:eq:extension-radial-formula`. `sum_coefficient_mul_pow`
  and `sum_abs_coefficient` prove its exact finite moments and coefficient
  mass. `radialPoint_mem_ball` proves every active input sample is interior.
* `radialAverage_eq_regularizedAverage` identifies each literal average
  with a fixed-kernel convolution. Its checked derivative bound costs one
  power of `R` per derivative and uses no positive input derivative.
* `exists_ballSmoothing_cartesian_bounds` applies the Section 3.1
  Cartesian-maximum convention on both sides for smooth-neighborhood
  representatives; the core construction itself only needs smoothness at
  every point of the original closed ball. The actual integer Sobolev norm
  is `LocalSobolev.cartesianJetNorm`, with each multiindex counted once.
* `affineSmoothing_vector_apply`, `affineSmoothing_matrix_apply`, and
  `affineSmoothing_ofReal` prove literal componentwise real action.
  `exists_ballSmoothing_vector_bounds` and `exists_ballSmoothing_matrix_bounds`
  additionally put the original coordinate-maximum input norms on the
  right hand sides, retaining the stronger Euclidean/Frobenius output bounds.

All constants precede the input and scale. Affine normalization changes
only fixed radius factors, never a derivative order or a power of `R`.
-/
