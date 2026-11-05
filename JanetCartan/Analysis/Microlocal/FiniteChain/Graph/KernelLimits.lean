module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Identification
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.SummedSupport
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CutoffSums
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.TestOutputs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fourier
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Shells
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Rescaling
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Support

/-!
# Regularized joint graph kernels and their test-input limits

Checked prerequisites for `app:ch_regular:eq:joint-kernel-phase`:
phase products in both literal orientations, compact primitive integration
carriers, absolute integrability, and the exact three-frequency normalization
and Jacobian. Product-volume Fubini identifies the literal forward and reverse
compositions with the full joint matrix kernel, also for normalized localizers
at physical frequency `ρ`.

Finite independent graph/output shell sums are actual frequency cutoffs in
these compositions. Summable pointwise matrix-kernel bounds prove convergence
of those compositions on continuous integrable inputs to testing the summed
kernel. Both amplitude positions, source shoulders, and the identity term remain.

For a fixed smooth compact graph-frequency cutoff supported away from zero,
the right quantization is smooth and the graph output is smooth and compact.
Fourier inversion therefore identifies output-cutoff removal with the actual
`forwardLeakage` or `reverseLeakage`, including `I - Mout`. Compact output
support is proved at this limiting stage, without asserting it for the finite
identity regularizations.

Absolute summability allows output-frequency summation first. Every recovered
row has one fixed physical carrier, so the genuine summed test action has that
carrier too. A fixed smooth output cutoff equal to one there preserves the limit.
Primitive smoothness and compact carriers give concrete supported matrix-entry
kernels in Cartesian coordinates. Summable bounds on their actual output jets
construct unique channel extensions through `Retarded.KernelSobolev`, with all
completed jets identified. The existing Hilbert matrix assembly retains the
explicit fixed channel factor. Exact measure-preserving coordinate transport
identifies each regularized channel action with its physical integral.

`exists_jointKernel_physical_extension` identifies the completed matrix action
with the full physical summed action, removes the fixed output cutoff using
the recovered support, and proves almost-everywhere convergence of the literal
finite-cutoff compositions to its zeroth completed jet in both orientations.
The extension retains all completed channel jets and the fixed `r*r` norm factor.

The exact remaining estimate inputs are uniform summable Frobenius bounds for
the uncut shell kernels, and uniform summable Cartesian output-jet bounds for
their cutoff matrix entries. The parent must transfer and instantiate the
`jc-graph-factor-kernel-estimates` estimates on these same shells, including
bounded frequencies and source shoulders, and supply the physical coordinate
measure and cutoff plateau. This module does not assert the unconditional factor estimate
`app:ch_regular:eq:chain-tail` or identify a nonintegrable raw Bochner graph
operator with its oscillatory realization.
-/
