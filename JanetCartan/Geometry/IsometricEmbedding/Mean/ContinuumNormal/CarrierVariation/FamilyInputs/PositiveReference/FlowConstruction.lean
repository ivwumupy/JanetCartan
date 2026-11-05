module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Family
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.OutputBuffers

/-!
# Actual positive null-flow construction and primitive comparison

`FlowConstruction.exists_restricted_positive_family_dependence` selects the
actual charts for every geometrically admissible immersion, before the output
order and tolerance, and proves their joint primitive comparison. The only
remaining input differences are projected stress, the actual Hamilton gradient
and the immersion.

`FlowConstruction.exists_restricted_positive_charts` constructs the literal
projected-stress coefficients and the SAME `UniformFlow` forward/inverse maps,
retaining the common open domain, compact coefficient ball, low direction
bound, adapted buffer and exact existence time. The admissibility threshold
precedes the supplied open restriction, so matching a Hamilton target does
not discard a reference already satisfying its strict margin.

`Chart.scalar_spec` proves the prescribed positive scalar problem for
`carrierScalarAmplitude`; `Chart.densityFootpoint_spec` proves a fixed compact
range for the literal density footpoint. Scalar one is allowed.
`exists_compact_output_balls` supplies concrete fixed output buffers.
`Chart.exists_primitive_transport_sub_tolerance` instantiates the published
coefficient and ODE implications on fixed compact output cylinders for these
retained maps and the fixed smooth positive initial scalar.

Consumer: `PositiveReference`, for `app:ch_background:prop:bg-frame` and
`app:ch_osc:prop:osc-normal`, Step 4'. Source of the construction:
`app:ch_waves:thm:leading`. The parent still owns immersion-to-Hamilton
comparison, target matching and final immersion-level epsilon-delta assembly.
-/
