module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.NormalCoordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Rescaling
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.FrequencyIntegration
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Regularity
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Limit

/-!
# Localized retarded Fourier kernels

Exact identities for `app:ch_regular:lem:finite-chain`, “Retarded and signed
factors”, and `app:ch_regular:eq:chain-tail`:

* concrete lower and literal upper amplitudes with the published packed phase,
  both weight positions, the right input and left output symbols, and an
  explicit output frequency regularizer;
* exact half-space substitutions for the buffered literal operators, keeping
  their respective scalars `i` and `-i` and their common transverse fiber;
* both radian Fourier normalizations and the full frequency-rescaling Jacobian;
* smoothness of the amplitudes and the right input quantization, joint absolute
  integrability of every regularized integrand, and physical Fubini identities
  identifying the full regularized operator compositions;
* Fourier reconstruction of the identity contribution, applied to the actual
  smooth compactly supported retarded outputs.

`localized_lower_eq_fourier_limit` and `localized_upper_eq_fourier_limit` give
the exact representation of `(I - Mout) A Min` by limits of the concrete kernels.
The upper formula retains the literal adjoint scalar `-i` and reversed
translation, separately from signed conjugate partners. The complementary
symbol is regularized before integration; its identity contribution is recovered
by proved Fourier inversion. Leakage estimates are the consumer's responsibility.
-/
