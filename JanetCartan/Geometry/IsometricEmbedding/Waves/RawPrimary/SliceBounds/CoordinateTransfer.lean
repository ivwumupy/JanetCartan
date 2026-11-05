module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.WeakPairings

/-!
# Actual coordinate and Frobenius transfer for raw slices

For `app:ch_waves:eq:individual-raw-slice`, this module supplies:

* `adaptedPhysicalCoordinates`: the measurable equivalence built from the
  retained `AdaptedSection`, preserving the actual full product and Euclidean
  volumes in both directions;
* `adaptedL2Equiv`: the complex L² coordinate equivalence, with both AE
  representative formulas;
* `SingleChannel.matrixChannelEquiv` and `matrixChannelL2Equiv`: the actual
  complex Frobenius/component equivalences, with integral compatibility;
* `physicalMatrixL2Equiv`: the combined isometry from the full output of
  `exists_rawSliceBandOperator` to physical matrix-valued L²;
* directional derivative integral identities from the actual continuous
  linear maps of `app:ch_seed:prop:seed-phase-charts`.

Both complex quadratures are retained throughout. No channel estimate,
raw-family bound, transported measure, or measure identity is assumed.
The parent raw slice construction supplies differentiated estimates and weak
jets and assembles the final Sobolev bound using these transfer identities.
-/
