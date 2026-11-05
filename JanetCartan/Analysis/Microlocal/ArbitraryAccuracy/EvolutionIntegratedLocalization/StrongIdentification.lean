module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.StrongLimits
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.PhysicalCutoffs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.OutputCutoff
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ProducerCutoffs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.ActualOperator

/-!
# Identification of localized elapsed regularizations

The strong limits use the same actual `elapsedGraphIntegral` and its literal
Hilbert adjoint (`app:ch_regular_base:eq:fixed-time-representation`). The
finite physical shell sums are exactly the independently cut forward/reverse
compositions, and a summable pointwise elapsed-shell majorant identifies their
physical test limit. `ShellSummation` and `UniformDecay` produce that majorant.

Compact physical symbols now construct one pair of bounded L² localizers for
every finite graph. Compact-kernel uniqueness extends the finite test actions
to the continuous right-localized input. At each fixed elapsed time and graph
cutoff, removing the independent output cutoff recovers the same bounded
localized graph. Graph-shell prefixes agree eventually, uniformly on the
producer's closed frequency carrier, with a cofinal dyadic subsequence of its
original regularizations, also in literal adjoint order.

The independent output prefixes are the existing contractive physical Fourier
multipliers. Their literal composition with the complement and the finite graph
represents the finite joint kernel. Compact exhaustion identifies the elapsed
L² integral even though its regularized identity term has noncompact output.
The two frequency cutoffs converge independently to the localized elapsed
operator. Almost everywhere uniqueness of the physical and strong L² limits
then identifies the summed kernel with that same operator and its literal
adjoint.

`exists_localized_elapsedGraphIntegral_shell_identification` assembles this
deduction from the primitive finite realizations, LOW bound, measurability,
per-r strong limits, fixed carriers and physical-kernel regularity. The exact
pointwise summable elapsed-shell majorant remains conditional on
`ShellSummation` and `UniformDecay`. The parent must instantiate these inputs
and prove the final Sobolev estimate `app:ch_regular:eq:chain-tail`; this
identification does not assert that unconditional quantitative estimate.
-/
