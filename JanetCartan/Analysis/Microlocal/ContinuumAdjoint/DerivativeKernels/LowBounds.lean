module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactSupport
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Size
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Frequency
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.NormalEstimate
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Assembly

/-!
# Modified half-order carrier L² bounds

The theorem `exists_modifiedAdjoint_L2_bound` proves the low L² estimate in
`app:ch_background:prop:bg-adjoint` for an arbitrary complex full amplitude.
Primitive mixed half-order symbol jets and quantitative conic geometry give
the order-zero full normal, with both measurement positions and all cutoffs
retained. The physical-to-cycles normalization includes the factor `(2π)^n`.

The actual regularized normal is identified with the scalar entry of the
checked matrix PDO. A concrete smooth compact exhaustion has a proved uniform
primitive jet reserve; Fatou removes it and constructs the unique bounded
realization of the literal `chartAdjoint` on all Euclidean measurement L² data,
with the shared carrier measure `dz dη`. The constant precedes the amplitude
and its budget. Instantiating the explicit primitive symbol, support, and
conic-chart hypotheses for the manuscript's data belongs to the consumer;
no normal identity or operator estimate is assumed by the assembled theorem.
-/
