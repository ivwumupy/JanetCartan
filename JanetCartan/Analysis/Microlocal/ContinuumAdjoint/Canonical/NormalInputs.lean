module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Construction

/-!
# Canonical geometric inputs for the raw adjoint endpoint

The working conic chart retains the published canonical coordinates, forward
map, inverse and Jacobian. Its domain is restricted to the fixed phase-agreement
buffer at both positions. Whole-domain phase matching, qualitative geometric
regularity and the degree-one determinant gap are proved from the retained
canonical geometric producers (`app:ch_background:prop:bg-adjoint`).

`exists_projected_normalInputs` instantiates the canonical geometric and
coefficient-buffer producers. It supplies the finite normalized jet reserve
through `2 * (n + 1)` from an immersion bound at order `2 * (n + 1) + 6`,
the closed high-frequency supported image, and every geometric input of the raw
scalar-transport endpoint. All constants precede the immersion. Global smoothness
and original-mask support of the amplitude belong to the canonical amplitude
producer; finite-family instantiation and endpoint application remain with the
parent adjoint construction.
-/
