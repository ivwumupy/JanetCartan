module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Realization

/-!
# Literal annular input dilation for raw waves

The normalization preceding `app:ch_waves:eq:sampling-prefix-normal` and used
in `app:ch_waves:thm:individual` is an actual complex linear isometry equivalence
on the restricted Lebesgue annuli in dimension `n - 1`. Its inverse, exact
half-derivative kernel substitution, Fourier scalar, adjoint, and full output
normal identities are proved here, including finite weighted rows and every
unchanged radial prefix.

The phase statements retain the physical covector: identifying a homogeneous
physical phase with the shifted quotient explicitly requires positive
homogeneity. For supplied bounded raw operators, `dilatedRawPrimaryOperator_ae_integral`
derives the normalized kernel from their original raw kernel representation.
Actual WKB amplitudes, boundedness, and that original representation must be
instantiated by the raw-primary and masked-normal producers. No Cᵐ or slice
estimate, torus/Lebesgue identification, or unconditional sampling theorem is
claimed. This input-space unitary is distinct from the output normal-amplitude
frequency substitution in `NormalComparison.FrequencyNormalization`.
-/
