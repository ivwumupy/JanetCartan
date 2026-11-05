module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.MatrixCarrier

/-!
# Source convergence for the original continuum normal amplitude

Primitive finite symbol jets discharge the four source integrability inputs of
`TransportKernel.realNormal_principal_reduction_of_test_limit`. The literal
frequency-cutoff full matrix kernels and the original squared radial carrier
regularizations converge on compact physical source and
output tests, with a uniform integrable source-Fourier majorant and one high
norm. Reflection, `k = 2πξ`, and the original Taylor remainder are preserved.

The primitive chart and coefficient norm producer is instantiated in
`SourceConvergence.PrimitiveBounds` and `SourceConvergence.RegularizedBounds`. The parent construction supplies the actual
geometry, and identifies its torus tests and carrier regularizations with these
Euclidean source-tested integrals. No unconditional normal identity or equality
of torus and Euclidean measures is asserted here.

Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`.
-/
