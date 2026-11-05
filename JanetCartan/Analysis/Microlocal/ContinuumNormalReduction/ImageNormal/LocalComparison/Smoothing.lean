module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.TestAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.Smoothing.VectorSobolev

/-!
# The local image-normal remainder

The explicit two-factor kernel and its bounded complex vector L² realization
for `app:ch_background:prop:bg-frame`, Step 1. Source integration by parts
and output differentiation identify its action with `P R P*` on compact
Schwartz tests. Both the operator and its literal Hilbert adjoint map L²
to H¹ with a common finite constant for the fixed cutoffs and smooth
coefficient arrays. The adjoint reverses the spatial arguments and
transposes the component indices, without a symmetry assumption.

`TestAction` instantiates the differential identity with the concrete
localized Bessel remainder. `VectorSobolev` discharges all scalar Sobolev
premises using the proved smooth compact matrix entries. The real-vector
bridge and assembly into the full periodic comparison belong to the parent
construction.
-/
