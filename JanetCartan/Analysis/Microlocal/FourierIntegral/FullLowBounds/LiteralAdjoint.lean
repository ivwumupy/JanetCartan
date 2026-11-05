module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.Graph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.Cutoff
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.Symbol

/-!
# Compact full-graph adjoints and reverse weak limits

The literal identification needed by `FullLowBounds.Uniform` is derived from
smoothness, compact support and Fubini. The forward realization on smooth
compact tests is the only operator-identity premise. The reverse weak limit
then follows from the strong convergence of the actual regularized adjoints.

The fixed frequency mask preserves all amplitudes on the closed carrier and
excludes zero for `SobolevBounds.IntegerBounds`. Conjugate transpose preserves
the full mixed symbol budget exactly. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1,
`app:ch_regular_base:eq:actual-adjoint-trade`, and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/
