module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Construction

/-! # Actual positive transport with independent full modulation

`LeadingWave.FullModulation.exists_positive_amplitude` constructs the actual
flow, footpoint and the published literal `scalarAmplitude` from the named
coefficient inputs. It preserves both `z` and `ζ`, attains the original datum
`r(y,z)`, solves the scalar and reduced transport equations, and retains joint
scalar/vector estimates with reserve 13 and an explicit common positive lower
bound. All constants precede the varying frame, immersion and initial datum.

Sources: `app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`.
The leading-wave parent retains the actual coefficient-producer instantiation,
carrier compatibility, and finite cover; this module does not assert the
unconditional source theorem.
-/
