module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Derivative

/-!
# Actual normal operators from the local uniform data

Constructs the full-input oscillatory operator with `normalOperatorScale`, its
actual Hilbert-adjoint normal composition and literal full matrix kernel for
`app:ch_osc:prop:osc-normal`. The scalar cutoff kernels are globally smooth and
compactly supported. Exact `pairedTransportCoefficient` channels are realized
with fixed L∞ mask symbols. Smooth localizations identify their sum with the actual operator-norm
derivative within the closed parameter interval, including both endpoints.
The velocity identity is discharged using the actual averaged-gradient inverse.
No uniform operator bound or final ε/h estimate is claimed.
-/
