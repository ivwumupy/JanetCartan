module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.Derivatives
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.WeightedVolumes
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.KernelSplitting

/-!
# Quantitative geometry of the fixed physical frequency cutoffs

The actual cutoffs for `app:ch_regular:eq:joint-kernel-phase` have checked
annular carriers, derivative profiles from the fixed bump, uniformly bounded
overlap, scale-relative annular counts and volume sums, and summable weighted
carrier volumes for independent graph/output indices. All contracting graph
annuli remain present; dimension zero has empty low graph carriers.

The physical kernel splitting is proved from primitive continuity and compact
carriers using cutoff linearity. The comparable/noncomparable analytic pair
estimates and their final physical-shell assembly are separate consumers of
these results, not assumptions used to prove them.
-/
