module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Retained

/-!
# Background tensors of the actual retained primary fields

For `app:ch_waves:eq:background-quadrature`, `localizedBackground` is defined
from the differential of the SAME original zero-input `fullPrimaryAtom`.
Its phase cancels, and `localizedBackground_eq_polynomial_of_leading_outputs`
identifies it with the full WKB polynomial using only the retained leading
regularity outputs. The polynomial's zero endpoint is the original transported
rank-one tensor.

`exists_retained_backgroundPolynomial_budgets` applies the actual joint
polynomial producer to the original immersion and scalar profiles and retained
leading/correction budgets. `exists_retained_supportedBackground_budgets`
constructs a globally smooth compact extension with the same joint reserve.
All constants precede the varying fields, inverse frequencies and scale.
The extension preserves the prescribed physical tensor on its fixed plateau.

`exists_retainedBackground_estimates` constructs the actual carrier pullback
and compact Lebesgue-L2 tensor, proves agreement with the original measured
background and transported tensor, and applies all three estimates to this
SAME family: deterministic quadrature at `p = 2*n-1`, physical `C^r` rough
bounds, and the colored-to-transport `O(λ⁻¹)` comparison. The rough estimate
is stated directly for the original differential. Constants precede the
varying fields, radial labels, frequencies, amplitude scale and shifts.

The input profiles and leading/correction estimates are the retained primitive
outputs of `RawPrimary.exists_finite_retained_graded_raw_family_with_primitives`.
The sampling parent retains their common finite-family application; this
module does not assert the full sampling or isometric embedding theorem.
-/
