module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.LowReserve

/-!
# Jets of the actual direct-evolution transfer coefficient

The literal averaged Hessian, averaged external gradient and inverse-adjoint
coefficient of `paper-v2.tex`, `new:eq:carrier-coefficient`, for the original
`paper.tex`, `app:ch_response:eq:direct-envelope-profile`.

Joint smoothness follows from primitive smoothness on the same open convex
product. The quantitative endpoints derive critical-map jets from its
equation and retain a positive coefficient reserve. Primitive phase jets
through order `N + 2` suffice for coefficient jets through order `N`.
`exists_transferCoefficient_lowJet_profile` gives the original `C k * L^k`
budget through `c + k` low coefficient orders, with constants before the
scale and phase family. The input scale remains separate.
-/
