module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.CriticalInverse
public import JanetCartan.Analysis.Microlocal.FullSourceStationary.CappedStationary

/-!
# Uniform stationary geometry of the original full source

The original `T.fullSourcePhaseInCoordinates i Q` retains its independent
`Euclidean 3 × Euclidean d` source parameters. The checked construction fixes
one source-parameter cap, coefficient threshold and elapsed interval before
histories and operators. It supplies both literal orientations, zero critical
value, full integration-segment containment in the original conic domain, and
uniform inverse averaged-Hessian bounds.

`exists_uniform_full_source_stationary_inverse_maps` realizes the stationary
and inverse specification from the original root/chart inputs.
`exists_uniform_full_source_critical_inverse_maps` also retains zero value and
joint phase smoothness using the same retained evolution's Hamilton--Jacobi
differential, homogeneity and endpoint identities. The source and joint phase
profiles keep coefficient shift one and history reserve `Rstar+3`.

For choices that must precede the common reference,
`exists_full_source_stationary_inverse_maps_of_coefficient_cap` and
`exists_full_source_hessian_inverse_stability_of_coefficient_cap` choose the
interval and inverse bounds from a fixed coefficient C4 cap and the supplied
source-incidence geometry. `exists_full_source_low_phase_budgets_of_coefficient_cap`
derives their low phase budgets from the actual phase producers, without a
reference or history. `exists_reference_tolerance_for_stationary_coefficient_cap`
supplies the universal `stationaryCoefficientCap` for the SAME later initialized
reference by applying the original C6 history-admission theorem at tolerance
at most one. Its reference tolerance precedes `G`; only the later initial-scale
threshold and all-order history grades may depend on that single reference.

The finite source-incidence selector must retain these SAME returned radii
through its masks and actual operators. Consumers: the fixed-response radius
and response-transfer constructions for `app:ch_response:eq:fixed-factor-transfer`
and `app:ch_response:eq:direct-envelope-profile`. This leaf does not assert the
unconditional `main:thm:main`.
-/
