module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support.Image

/-!
# Supported geometry for the canonical raw adjoint endpoint

The original closed masks with threshold one lie in the phase-restricted
canonical chart. Their actual image is closed and contained in its actual
output domain, and the unchanged inverse retains the high-frequency bound.
The compact parameters, nesting, `hdom`, and `hJ` are supplied by `Support.Inputs`;
the image and inverse-frequency results are supplied by `Support.Image`.

Consumer: `exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Source: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-full-complex-amplitude`.
-/
