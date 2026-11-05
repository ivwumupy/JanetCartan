module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.CoefficientImplication

/-!
# Fixed-reference dependence of the positive null flow and scalar

`NullFlowDependence.exists_cNorm_carrier_transport_sub_lt` proves the combined
finite-order implication from primitive `carrierTransportDirection` and
`carrierTransportPotential` differences to differences of the SAME retained
forward map `Φ`, inverse ODE map `Y`, and literal `carrierScalarAmplitude`.
For each order `m` and positive tolerance it chooses `q = m` and a positive
coefficient threshold before the varying frame, immersion, tube and maps.
The output sets are fixed compact inner cylinders and physical/carrier domains.

`NullFlowDependence.exists_cNorm_carrier_characteristics_sub_lt` proves the
finite-order implication from primitive `carrierTransportDirection`
differences to differences of the SAME retained forward map `Φ` and inverse
ODE map `Y`. The threshold precedes the varying coefficients and solutions;
order `m` of the direction suffices for order `m` of both maps. Independent
comparison lifts are constructed on the original low-bound buffers and
identified with the retained maps by ODE uniqueness and reversal.

The hypotheses are the original common coefficient buffer, smoothness and low
bound, together with the initial, range, ODE and inverse identities produced by
`ActualAmplitude.UniformFlow` inside `ActualAmplitude.LocalConstruction`.
`exists_densityFootpoint_sub_tolerance` transfers the inverse difference to
the actual physical/carrier footpoint using `densityCoordinates`.

Consumer: `FamilyInputs.PositiveReference`, for `app:ch_background:prop:bg-frame`
and `app:ch_osc:prop:osc-normal`, Step 4'; source of the ODE construction:
`app:ch_waves:thm:leading`.

The scalar comparison is proved through the actual oriented characteristic
integral, exponential and inverse substitution. Compact cylinders remain inside
the original flow domain; no time interval is enlarged to fit a ball estimate.
The fixed initial scalar is smooth and positive on the original open label
ball `ball p₀ (R / 8)`, covering every compact composition buffer selected by
the proof. Scalar one satisfies these inputs for the base coefficient consumer.
The density footpoint is exactly
`Y (FlowAmplitude.coordinates e (x, parameter z))`.

The parent separately owns immersion-to-direction/potential comparison and
actual instantiation of the common buffers. None of these conditional
deductions certifies the parent's immersion-level existence theorem or the
original wider uniform positive-density class.
-/
