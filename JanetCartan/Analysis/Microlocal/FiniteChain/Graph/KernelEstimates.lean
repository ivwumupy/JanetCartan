module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Assembly

/-!
# Kernel estimates for graph factors

Primitive product grades, actual output derivatives, comparable-frequency decay,
and absolutely summable noncomparable shells (`app:ch_regular:eq:chain-tail`).
`exists_regularizedGraphKernel_graded_bounds` combines the estimates with fixed
frequency and grade losses independent of accuracy. The noncomparable gaps are
derived from physical covector comparison using the literal rescaled phase.
The exact comparable joint gap remains the buffered-localizer producer's input.
The parent must instantiate the primitive grades and carriers; operator
identification and regularization limits belong to `Graph.KernelLimits`, and
the parent performs the final `Retarded.KernelSobolev` operator assembly.
-/
