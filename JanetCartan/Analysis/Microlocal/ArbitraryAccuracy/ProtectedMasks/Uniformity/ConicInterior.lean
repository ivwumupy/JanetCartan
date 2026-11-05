module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.ConstructorInputs

/-!
# The full conic interior relation and coefficient-uniform gap

`exists_uniform_radial_nested_localizers_and_gap` constructs the finite radial
proof refinement and actual nested masks, and proves the full-gradient gap
for the original conic phase and its supported extension on the entire fixed
radial carrier. All choices precede the coefficients and requested accuracy.
`fieldRoot_maskAssembly_primitives` matches the exact primitive root outputs
of `UniformGeometry.exists_uniform_fieldRoot_conicGeometry`.

Both orientations, actual physical factor masks, whole physical segments,
full diagonal, original elapsed interval and source shoulder are retained.
Actual finite selection of the original characteristic and comparison charts
remains with the arbitrary-accuracy parent. The uniform radial construction
assumes neither successful masks nor a new conic gradient or speed gap.

Consumers: `exists_uniform_nested_localization_data` and
`finiteChain_observation_rapidDecayAt`, for `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:joint-stationary`, `app:ch_regular:eq:chain-tail`, and
`app:ch_regular:thm:no-return`.
-/
