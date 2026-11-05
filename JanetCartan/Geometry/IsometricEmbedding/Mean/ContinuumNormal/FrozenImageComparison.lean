module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SmallSupport

/-!
# Frozen periodic image normal and its Euclidean multiplier

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, these results compare
the literal periodic/source-mask image channel from `paper.tex`,
`app:ch_background:defn:bg-row`, with its frozen Euclidean multiplier.

`exists_imageChannel_fourierIntegral_comparison` proves exact norm preservation
under cell zero extension and an L¹-squared energy error, with a constant fixed
before the inner radius. The ordinary Fourier integral uses complex Euclidean
fibers, the real part of their pairing, and physical frequency `2πξ`.
The periodic correction includes both cross terms and the remainder square;
the source correction includes the source square between both Bessel factors.
All analytic premises are discharged for these same fixed operators.

`exists_small_support_imageChannel_energyDifference_le` absorbs the error
using the actual physical support volume while leaving both outer masks fixed.
All results hold for supported real L² inputs, including dimension zero, with
coefficient agreement required only on the measurement plateau. The full
image/carrier coercivity and its geometric instantiation belong to the parent
continuum-normal construction.
-/
