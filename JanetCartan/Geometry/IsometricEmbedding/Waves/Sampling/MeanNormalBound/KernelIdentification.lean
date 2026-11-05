module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.SmoothFullPhase

/-!
# Euclidean kernel disintegration for the sampling mean

The kernel/disintegration bridge for the mask-free proof following
`app:ch_waves:eq:sampling-operator-bounds`:

* The original wide-band kernel is constructed from `BandKernelData.column`.
  Its forward map, adjoint, and normal are identified with both sharp Hilbert
  components through `bandRefinement` and `wideRefinement`.
* The original smooth `radialBand` factor removes the remaining wide-band
  indicator before smooth symbol calculus.
* The exact original weighted mean, with every chart, color and band, is the
  spectator integral of constructed `fullBandKernelOperator` normals.
  All measures are literal Lebesgue measures, and the output is full Euclidean
  vector-valued L². Adjoint and Bochner/Fubini identities are proved from columns.
* Both real quadratures and the factor four are retained.
* Primitive phase, measured amplitude and cutoff matching identify the actual
  forward operators, adjoints and normals with
  `NormalComparison.uniformOscillatoryOperator`, after the literal input
  dilation `η = 2^j θ` and an isometric finite output-coordinate change.
  The full two-position kernel retains its absolute inverse Jacobian.
* `exists_smooth_majorants_fullPhase_normal` constructs the smooth angular
  cutoffs before frequencies, bands and colors, and proves domination of the
  original unmasked mean by the actual full-phase normal sum. All spectator
  integrability is proved; the band sum is inside that integral.

The exact original-weight identity uses only continuity of `sqrt ψ`. Smooth
full-phase calculus uses the constructed majorant instead; no smoothness of
`sqrt ψ` is assumed. The scale `2^j` is `dyadicScale (j + 1)`, while
`dyadicScale j` itself is `2^j / 2`.

The actual same-object matching inputs must come from
`RawPrimary.Construction.fullPrimaryWave`, its leading amplitudes and the actual
`FullPhaseCharts`, together with the buffered support of their fixed cutoffs.
Those same-object instantiations remain with the sampling parent. This is a
completed conditional kernel bridge, not the unconditional frequency-uniform
mean bound: the dyadic estimate and its supported phase gap are separate
obligations, and no operator norm estimate or `hmean` is a premise here.
-/
