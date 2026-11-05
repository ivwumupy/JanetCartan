module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PhysicalDerivatives.Chart

/-!
# Physical derivatives of the partial inverse adjoint transform

Actual Fourier-side initial radian multipliers and carrier derivatives become
physical weak coordinate derivatives after partial inverse Fourier transform,
with the original carrier measure. At every finite order, joint smoothness
and L² membership of the actual derivative words construct a compatible
`CarrierL2DerivativeFamily`. Plancherel and the shared physical norm comparison
bound `physicalSobolevNorm s` by `(4π)^s` times the finite word L² norm sum.

For `app:ch_background:prop:bg-adjoint`, the chart application derives joint
smoothness by compact measurement integration and uses the checked `Iteration`
identities to bound the physical norm by the realized expansion term L² norms.
The parent raw adjoint construction still supplies the primitive geometry,
termwise L² membership and quantitative conic/interpolation bounds. This
transfer theorem does not by itself assert the unconditional raw adjoint bound.
-/
