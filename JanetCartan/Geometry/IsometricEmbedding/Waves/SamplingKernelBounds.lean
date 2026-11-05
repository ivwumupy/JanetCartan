module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.BernsteinInputs
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.OutputBasis

/-!
# Actual annular sampling kernels

Conditional kernel deductions for `app:ch_waves:eq:sampling-operator-bounds` and
`app:ch_waves:eq:sampling-prefix-normal` in paper.tex.
`BandKernelData` contains the explicit real phase, continuous mask and measured
amplitude, compact physical support, and uniform amplitude/mask bounds. From
these analytic inputs its `operator` is constructed on `RawInputRealization.AnnularL2`
with full output `L²(Euclidean n; EuclideanSpace ℂ (Fin n))`. The literal integral
and adjoint formulas, operator-norm continuity, compactness, Hilbert–Schmidt
bound of order `R^n`, positive trace, and finite compression trace bounds are proved.
All completed results have no `sorryAx` dependency.

`BandKernelData.dyadicPrefix` constructs every prefix on the same full PiLp input.
Its literal band sum and exact sum-of-band-normal identity, continuity,
compactness and Hilbert–Schmidt estimate are proved from the kernels. The bound
on its squared operator norm is conditional only on the sharper single-band
oscillatory estimate and the dyadic ceiling. Common kernel bounds produce a
constant uniform over every prefix.

`BandKernelData.samplingFamily` instantiates the weighted-expectation helper,
discharging its continuity and Hilbert–Schmidt premises. Its expectation is both
the literal colored Lebesgue integral and the uniform-shift sample expectation.
Positivity, compactness, the exact integrated trace formula, and the mesh-independent
`C Λ^n` trace estimate are proved, including every finite compression and every
finite orthonormal diagonal sum. Centered sampling blocks are compact with the
required `C Λ h^3` bound. `outputHilbertBasis` supplies a countable basis of the
entire output for all these results.

The actual leading-wave and WKB producers must still instantiate the continuous
phase, mask and measured amplitude, compact physical support and common low
bounds in `BandKernelData`. `jc-raw-primary-slice-l2` supplies the separate
single-band oscillatory estimate. The sampling construction supplies the actual
continuous nonnegative window and compact patch bounds and fixes the dyadic
ceiling. These are the remaining analytic inputs to this conditional deduction;
no row, expectation-continuity or trace conclusion is assumed. The stronger
expectation norm estimate of order one requires the full normal-amplitude
comparison and does not follow from these trace bounds. Concentration and
successful-sample selection belong to the sampling construction.

Both input quadratures are retained by the `RealQuadratures` API.
`BandKernelData.real_dyadicPrefix_normal` proves the exact normal factor four
for the constructed kernels; the real row estimates are available in `Rows.Real`.
No input quadrature is projected out or identified with torus data.
-/
