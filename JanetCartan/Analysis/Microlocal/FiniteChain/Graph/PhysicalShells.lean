module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Cutoffs
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Identities
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.PhaseExtension
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Carriers
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Profiles
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.SupportedCarrier
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Summation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Assembly.Estimates

/-!
# Physical cutoff pairs for graph kernels

The physical-shell bridge for
`app:ch_regular:eq:joint-kernel-phase` and `app:ch_regular:eq:chain-tail`.
The frequency cutoffs are fixed independently of accuracy. Every graph
cutoff avoids zero, their sum covers all nonzero frequencies, and the output
partial sums are bounded by one and converge to one. Exact rescaling and
high/low splitting preserve the physical full amplitude and normalization.

`exists_physical_kernel_majorants` supplies summable majorants for the actual
independently indexed physical kernels, their evaluated output derivatives,
and their globally uniform zeroth norms. Their masses have the fixed-loss
form required by `KernelLimits.exists_jointKernel_physical_extension`.
Both frequency regimes and the shrinking low-frequency volumes are included;
`iteratedFDeriv_physicalGraphKernel_dim_zero` handles dimension zero separately.
Smoothness and quantitative phase estimates use the original conic domain,
with extension justified through agreement on the integration support.

The remaining hypotheses are the explicitly stated primitive phase, chart,
full-symbol and buffered-mask data. Their instantiation, Cartesian transfer,
and the final Sobolev operator assembly belong to the parent graph factor
construction; this module does not assert the paper's unconditional theorem.
-/
