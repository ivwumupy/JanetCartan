module

public import JanetCartan.Analysis.Microlocal.NormalComparison.ChangeOfVariables
public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskDerivative
public import JanetCartan.Analysis.Microlocal.NormalComparison.Comparison
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChannelBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.MaskSymbols
public import JanetCartan.Analysis.Microlocal.NormalComparison.UniformKernel
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus

public import JanetCartan.Analysis.Microlocal.NormalComparison.Assembly

/-!
# Exact masked normal comparison

Proves `app:ch_osc:prop:osc-normal` from the original buffered input data:

* `UniformNormalData.maskedNormalKernel_eq_inverse_integral` gives the exact
  two-position change of variables, including the absolute inverse Jacobian;
* `UniformNormalData.uniformOscillatoryNormalOperator_ae_maskedNormalKernel`
  identifies that kernel with the actual Hilbert-adjoint composition;
* `UniformNormalGeometry.exists_uniformOscillatoryOperator_bound` gives the
  frequency-uniform bound on the entire-input L² operator;
* `UniformNormalGeometry.exists_uniformOscillatoryNormalOperator_comparison`
  gives the `ε / h` estimate for any L∞ realization of the mask;
* `UniformNormalGeometry.exists_uniformNormalComparison` combines both bounds
  and constructs the mask realization, with a single uniform positive constant.

All inverse/coefficient estimates, the buffered scalar cutoff channel, the full
kernel realizations and endpoint derivatives are discharged from the input-only
setup. The proof retains both physical positions and the Jacobian and first mask
derivative terms. Constants are chosen before the family, frequency, mask and
parameter; no higher mask derivative bound is used.
-/
