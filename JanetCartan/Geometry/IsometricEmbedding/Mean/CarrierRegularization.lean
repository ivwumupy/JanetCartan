module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.Estimates

/-!
# Finite-frequency continuum carrier regularization

Actual compact complex operators on the published carrier and torus Hilbert
spaces, with literal source and Hilbert-adjoint formulas, the squared-kernel
Hilbert–Schmidt identity, and the rough `R^n` bound for the squared norm.

The geometric inputs remain explicit in `CarrierRegularization.MaskHypotheses`:
joint kernel and mask measurability, compact parameter support, finite frequency
support, a bounded real mask and the pointwise half-derivative amplitude bound.
The phase-chart, leading-wave and two-position amplitude constructions must
instantiate these inputs. No cutoff-independent operator bound, geometric
existence result, or uncut row is asserted here. Consumers are the continuum
row, its normal reduction, and its initial-variable adjoint construction.

Source: `app:ch_background:eq:bg-T` and
`app:ch_background:eq:bg-realification` in `paper.tex`.
-/
