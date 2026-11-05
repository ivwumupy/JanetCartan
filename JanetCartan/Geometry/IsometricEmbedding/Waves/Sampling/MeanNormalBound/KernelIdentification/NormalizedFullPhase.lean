module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.Kernel

/-!
# Normalized full-band identification with the actual full-phase operator

For `app:ch_waves:eq:sampling-prefix-normal`, the literal product input is
normalized by `η = 2^j θ`, changed to Euclidean coordinates, and extended by
zero. The input change retains `sqrt ((2^j)^(n-1))`. The physical half derivative
and Fourier factor are accounted for by `fullPhase_fourier_normalization`.
The existing `finiteL2CoordinateIsometry` handles the full physical output.

Primitive phase, measured amplitude and cutoff matching imply the actual
forward, adjoint and normal identities, and the full two-position kernel of
`app:ch_osc:eq:osc-exact-normal-kernel`, including its absolute inverse
Jacobian. No estimate or normal-matching hypothesis is used. Both inputs are
extended to the same entire Euclidean L² space, so the open phase chart need
not contain the whole closed annulus.

The sampling parent must instantiate the primitive matching conditions using
the same `RawPrimary.Construction.fullPrimaryWave`, leading amplitude,
measurement/input/angular cutoffs and `FullPhaseCharts`. This module assumes
the supplied cutoff and does not construct the separate smooth majorant.
-/
