module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Sampling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Radial

/-!
# Stability of the complete signed carrier family

The signed-pair argument in `app:ch_seed:prop:seed-actual-menu`, Step 2,
`app:ch_seed:eq:seed-actual-chord`, and `app:rem:exhaustive-signed-pairs`.

`SignedPairs.signed_family_stability` takes quantitative frozen projected
pair bounds and uniform value/parameter-derivative errors. It proves all actual
projected bounds, the true frequency comparisons, and containment of the closure
of the normalized directions in one compact symmetric set with a quantitative
distance from `cubeBadSubspaceUnion`. Its physical index may range over the
entire current neighborhood, so the set is uniform over all current immersions.

`SignedPairs.radial_projected_pair` derives the cross-group bounds directly
from radial domination and the frozen dominant carrier's gap, for both signs.
The sampling lemmas include doubled plus phases and exclude the repeated-index
zero minus term. Distinct samples in a common group must have distinct parameters.

The inputs here are frozen geometry and actual `C¹` closeness, not an assumed
actual signed-direction gap. Construction of the frozen patches, actual phases,
and verification of those closeness inputs belong to their respective owners.
-/
