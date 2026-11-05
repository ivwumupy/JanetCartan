module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Family

/-!
# Uniform low bounds for the actual full-amplitude graph

`exists_fullGraphL2_of_primitive_inputs` constructs the full graph from original
full-symbol jets and the primitive phase/inverse/Jacobian/support geometry on
the whole averaged-gradient image. Its constant is chosen before the amplitude
and its budget; its dimension-dependent reserve is `3 * n + 4`, including budget
zero. The coefficient smoothness, carrier inheritance, normalized shell jets,
coefficient operators and summable source-series bounds are proved here.

The SAME literal full-amplitude frequency regularizations converge strongly,
as do their actual Hilbert adjoints. Each regularized adjoint is identified
with `reverseGraphOperator` of the conjugate-transposed amplitude and conjugated
cutoff. Both branches have the `GraphDistributionalRealization` required by
`SobolevBounds.IntegerBounds`; the forward graph also retains its original
unregularized test-integral realization.

`exists_fullGraphFamily_of_primitive_inputs` fixes one operator family and one
smooth compact cutoff sequence avoiding zero for every amplitude on the given
closed frequency carrier. The sequence preserves the original regularized
amplitudes exactly. The actual ordered weighted jets of `IntegerBounds` supply
the source-symbol budget without losing derivatives, so the same reserve and
constant apply to every admissible modified amplitude. Its weighted clauses
use any bracket dominating both one and the physical covector norm, including
`1 + ‖η‖`. Reverse amplitudes may have any physical carrier inside the fixed boxes.

The source masks, Frobenius matrix norms, Euclidean Lebesgue Hilbert spaces and
physical normalization `(2π)^(-n)` are unchanged. The full source-dependent
operator and its limits are assembled through the actual coefficient series.
These are checked deductions from the explicit primitive geometric inputs;
their concrete geometric instantiation and the final finite-calculus assembly
remain with the parent tasks. Source: `app:ch_regular_base:thm:actual-calculus`,
Step 1, `app:ch_regular_base:eq:actual-adjoint-trade`, and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/
