module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison.Frobenius

/-!
# Periodic jet and Sobolev comparisons for the mean recurrence

For paper.tex, `main:lem:mean-recurrence`, the higher factor in the integrated
Leibniz bound is controlled by
`periodicL2Norm_periodicJet_le_sobolev_uniform`, and the product's Sobolev norm
is recovered by `periodicSobolevNorm_le_sum_periodicJet_uniform`.

Both constants are at least one and depend only on the domain dimension and
order cap. The matrix variants apply to the actual real or complex Frobenius
norms. Smoothness supplies all summability; no Fourier-support or assumed
norm-comparison premise is required. The weighted product assembly remains in
the consuming derivative estimate.
-/
