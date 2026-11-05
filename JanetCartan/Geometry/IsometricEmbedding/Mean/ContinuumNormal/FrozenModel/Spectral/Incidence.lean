module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.RootGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.SelectedWeights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Incidence.Detection

/-!
# Positive weights and actual detectors at the frozen incidence roots

For `app:ch_background:prop:bg-frame` and
`app:ch_seed:eq:seed-actual-detection`, `SelectedWeights` combines the published
root geometry with the primitive pivot, minor and normal producers. It selects
a fixed minor before the frame, explicitly shrinks the frequency neighborhood
and root-error tolerance, and proves the frozen frequency equation, exact inverse
domain and root identity, original angular plateau, actual detector identity,
and strict positivity of the literal input weight at the geometric frequency
threshold. The Hamilton family, incidence refinement and constructed roots are
the same throughout. Allowed initial multipliers retain their fourth power.

`Detection` proves that zero reflected carrier energy annihilates the actual
root detector, conditional on primitive coefficient regularity and integrability
supplied by the independent spectral regularity construction. The spectral
parent must instantiate those inputs, construct the finite covering family at
one common root tolerance, and prove the final uniform gap. Shrinking local
frequency neighborhoods here makes no assertion that an old finite cover remains
a cover.
-/
