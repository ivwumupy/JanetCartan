module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel

/-!
# Finite matrix and vector integer PDO bounds

The natural-order finite matrix portion of `app:ch_regular_base:eq:fio-input`
and `app:ch_regular_base:thm:actual-calculus` on Euclidean Lebesgue L².

The four `exists_matrixTwoPositionL2Operator_*_all_data` and four
`exists_vectorTwoPositionL2Operator_*_all_data` theorems preserve natural
Sobolev order or gain one, for the actual operator and its literal Hilbert
adjoint. Their scalar estimates are discharged from `IntegerBounds`.
The factor is explicitly `card I * card J`, the coefficient budgets use the
Frobenius norm, and the vector norms are Hilbert norms with an exact coordinate
L² isometry. Low and high derivative shifts are unchanged by finite lifting.

The remaining inputs for geometric consumers are joint amplitude smoothness,
fixed two-position support, and the displayed primitive low/high Frobenius
budgets (weighted by exactly `1 + ‖ξ‖` for gain one). No matrix estimate is
assumed by the eight integer theorems. Literal kernel identities hold on compact
smooth data and preserve reversed source masks. The existing graph normal
operators are identified exactly. General graph phases, real Sobolev orders,
and geometric coefficient-budget production remain outside this deduction.
-/
