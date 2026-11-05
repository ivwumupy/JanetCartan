module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Geometry
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Volumes
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PairEstimate
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.PhysicalTransfer
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Majorants
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Estimates

/-!
# Noncomparable physical graph cutoff pairs

The actual independently indexed high/low graph and output cutoffs satisfy
uniform bounds for evaluated output derivatives, with summable pair weights
and fixed losses independent of accuracy. The input shoulder, both amplitude
positions, negative symbol orders, bounded output ball, and shrinking graph
volume are retained. Physical phase extensions are justified on the support.

The parent supplies primitive cutoff carriers, phase comparison and symbol
profiles, and assembles the comparable regime. The cutoff geometry producer
is `jc-graph-physical-cutoff-geometry`. These are conditional estimates for
`app:ch_regular:eq:joint-kernel-phase` and `app:ch_regular:eq:chain-tail`, not a
claim that the parent construction or the unconditional paper theorem is done.
-/
