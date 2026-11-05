module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableEstimates.Summation

/-!
# Graph shell decay by physical-base integration

For `app:ch_regular:eq:chain-tail`, actual output derivatives of explicitly
regularized graph shells are absolutely summable with fixed dimension, symbol
and grade losses independent of requested accuracy. The input normalization
remains `ρ`, while each physical-base integration gains `L/R` at the larger
shell radius. Both amplitude positions and all three Fourier measures remain.

The parent must instantiate the normalized phase gap and phase grades from the
separate geometry producer. Operator identities, removal of regularizers, and
combination with the comparable estimate remain the parent's obligations.
-/
