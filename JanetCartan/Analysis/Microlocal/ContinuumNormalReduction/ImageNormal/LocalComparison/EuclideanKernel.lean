module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.Convolution
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.Periodization

/-!
# Image Bessel kernel: heat integral, convolution, and torus periodization

For `app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-frame`,
Step 1, the explicit heat integral is nonnegative, Lebesgue integrable, and has
mass one. Its Fourier transform is exactly the published image Bessel symbol,
with physical covector `2πξ`, and convolution with it realizes the complex
Schwartz multiplier pointwise with absolute convergence.

The full integer-lattice periodization converges absolutely almost everywhere
on the fundamental cube and on the normalized torus. Its measurable torus
realization uses the centered representative, agrees with the literal lattice
sum at every Euclidean lift, is integrable with unit mass, and has complex
Fourier coefficients exactly `ContinuumRow.periodicBesselSymbol`.

These unconditional kernel identities supply the local comparison's
identification of the Schwartz tail. Off-diagonal derivative estimates and
the bounded-operator comparison are separate downstream obligations.
-/
