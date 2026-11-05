module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Real

/-!
# Actual annular Lebesgue Hilbert synthesis

This module constructs the complex bounded density synthesis, identifies its
adjoint and output normal, proves the square-root dyadic ceiling bound, and
provides coordinate-prefix projections on the shared `RawInputRealization.Input`.
Only afterwards are scalars restricted to the real Hilbert spaces of
`app:ch_waves:thm:individual` and `app:ch_waves:eq:sampling-prefix-normal`.

Conditional analytic inputs: the masks are AE strongly measurable and bounded
on their literal annular Lebesgue measures. Norm estimates use nonnegative radii
and mask bounds; the dyadic consequence additionally uses its stated ceiling.
The producer `jc-deduce-raw-input-realization` and the raw-primary,
current-canonical, and sampling consumers must instantiate these hypotheses.
No pointwise synthesis, Fourier-L¹ estimate, or torus identification is assumed.
-/
