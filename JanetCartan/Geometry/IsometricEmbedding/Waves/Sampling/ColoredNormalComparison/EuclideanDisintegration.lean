module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.SpectatorIntegrability
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.RawSlices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.BandKernel

/-!
# Euclidean common-kernel disintegration and spectator integrability

The deductions required by `exists_integrated_colored_prefix_transport_bound`
for `app:ch_waves:eq:colored-normal-comparison` and
`app:ch_waves:eq:sampling-prefix-normal`.

* `samplingNormal_eq_integral_compactSlice` derives the weighted single-band
  normal identity and Bochner integrability from a measure-preserving input
  coordinate map and the original normalized forward kernel. The patch weight
  enters by its square root, without division, and the masks are the literal
  finite colored masks pulled back by `z₀ + Z u`.
* `compactSliceOperator_eq_bandKernelOperator` identifies the slice with the
  actual band-kernel construction from a primitive kernel equality.
* `compactSliceOperator_eq_dilatedRaw` uses the existing raw-input dilation and
  its exact Fourier normalization to identify the same slice from a raw
  half-derivative kernel, preserving its entire output normal.
* `integrable_coloredPrefixNormal` and `integrable_transportPrefixNormal`
  discharge the fixed compact spectator integrals from primitive joint phase
  and amplitude continuity on the original buffered boxes. The input masks
  may use any exact L∞ representatives.

All outputs use literal Euclidean Lebesgue measure. The published output
conjugation and realification preserve both quadratures and the exact factor
four. The actual wave family, primitive kernel/coordinate equalities, and
common-history budgets remain obligations of the sampling and wave producers;
these deductions do not construct those data or assert the final theorem.
-/
