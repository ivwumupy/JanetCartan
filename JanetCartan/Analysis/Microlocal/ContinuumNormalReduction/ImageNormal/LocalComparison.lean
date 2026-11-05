module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealAssembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealSmoothing

/-!
# Local periodic–Euclidean Bessel comparison

For `app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-frame`,
Step 1, `periodicBesselInverse_localized_eq_add_remainder` identifies the
actual real periodic inverse, localized by two fixed smooth cutoffs supported
in a common cube strictly inside the centered cell, with the localized
Euclidean Bessel multiplier plus the explicitly constructed lattice remainder.
It acts on the full vector Lebesgue L² space. The actual restriction and zero
extension retain normalized torus volume and Euclidean Lebesgue measure.
The scalar theorem `periodicBessel_localized_L2_eq_add_remainder` also applies
to any bounded periodic operator with the specified lattice Fourier action;
the real theorem discharges that action using the actual periodic producer.

The heat integral has the required Fourier transform and an absolutely
convergent torus periodization almost everywhere, with the proved lattice
Fourier coefficients. Its nonzero lattice translates form a smooth remainder
on the comparison cube. Both orientations of the localized compact kernel
have global finite derivative budgets, including the two extra orders for
the normal factors. The lattice-sum/input-integral interchange identifies
this kernel with the Schwartz output tail; density extends the equality to
all L² inputs. No exact equality of Euclidean and torus kernels is asserted.

`periodicBesselInverse_localized_adjoint_eq_add_remainder` retains the literal
Hilbert adjoint and reversed masks. After both first-order normal factors,
`realLocalizedImageNormalRemainderOperator_schwartz_ae_coefficientOperator`
identifies the concrete real matrix-kernel realization with `P R P*` on
compact real Schwartz tests, including every zeroth-order coefficient term.
`realLocalizedImageNormalRemainderOperator_sobolev_one_bounds` gives a common
L²-to-H¹ bound for this error and its literal Hilbert adjoint. Their real
matrix integral formulas retain reversed spatial arguments and transposed
indices. All kernel, Fourier, reality, and smoothing premises are discharged.
The constants depend on the fixed cutoffs and smooth coefficients; these
results do not assert uniform tame bounds over varying geometric data.
-/
