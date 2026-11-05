module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Ceiling

/-!
# Actual Lebesgue initial Fourier synthesis

Checked conditional deduction of `app:ch_waves:eq:B-bounds` in paper.tex. The
input is the real Hilbert space underlying a finite sum of complex `L²` spaces
on initial Euclidean annuli, using Lebesgue measure in dimension `n-1`.
`density` is the literal masked half-derivative sum and `field` its radian inverse
Fourier integral. The leaves prove almost-everywhere density linearity, pointwise
field linearity, input support, all polynomial moments, smoothness, and the
Fourier `L¹` and initial `C^m` estimates with constants independent of band count.

The quantitative ceiling theorems use geometric radii `2^ℓ`, `ℓ < J`, with
`2^J ≤ C K`; masks are measurable and uniformly bounded. Actual wave producers
must supply those masks and the ceiling. No torus/Lebesgue identification,
canonical-adjoint estimate, zero-atom modification, WKB identification, or
physical slice Sobolev estimate is asserted by these initial-data results.
-/
