module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.MaskedChannels

/-!
# Compact oscillatory operator calculus

The actual scalar and finite-vector integral operators for
`app:ch_osc:prop:osc-normal`, including their Hilbert adjoints, operator norm
parameter differentiation, and the literal full normal kernel. The derivative
of the actual normalized normal operator has the transported two-position
integral, with exactly the manuscript's coefficients and normalization squared.
The fixed scalar cutoff preserves these coefficients and gives the existing
`fullNormalAmplitudeKernel` entrywise.

`exists_compactOscillatoryNormal_maskTransportChannels` constructs the mask
multipliers and all bounded matrix channels and identifies their sum with the
actual operator norm derivative. Both integrals are distributed with all
integrability premises discharged from smoothness and compact support.
Only the mask value and first-derivative bounds are required. The phase-velocity
identity is needed only on the original amplitude carrier; the parent supplies
it from the averaged-gradient inverse and retains the uniform-in-frequency
estimates and final parameter comparison.
-/
