module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Joint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Conic
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Regularized

/-!
# Support and regularity for the actual differentiated adjoint amplitudes

For `app:ch_background:prop:bg-adjoint`, every term of
`adjointDerivativeExpansion` is jointly smooth and supported inside the
original joint topological support. Closed primitive conic buffers therefore
supply the carrier, angular, high-frequency and compact measurement support
inputs to `exists_modifiedAdjoint_L2_bound`. The original chart regularity is
reused, and its geometric buffer must cover both copies of the closed
primitive amplitude support, not merely its pointwise nonzero set.

The regularized chart and source support sets are constructed once from the
primitive buffer and the existing `modifiedCarrierCutoff`. Their compactness,
source inclusion, density vanishing and chart continuity are proved uniformly
for all generated terms. The parent supplies smooth slice coordinates (and
continuous inverse coordinates), the common chart-domain inclusion, forward
continuity and the closed conic image buffer from its actual geometry.

`norm_iteratedFDeriv_scaledOriginalAmplitude` identifies the derivative norms
in the two product associations exactly. The quantitative `mixed_jets` field
of `PrimitiveAmplitudeReserve` remains the independent reserve-interpolation
obligation. No generated jet estimate or operator bound is assumed here.
-/
