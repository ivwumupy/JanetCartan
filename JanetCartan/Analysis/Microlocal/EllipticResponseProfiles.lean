module

public import JanetCartan.Analysis.Microlocal.EllipticResponseProfiles.FullSourceProfiles

/-!
# Reserve-preserving full-source profiles for the actual elliptic response

`exists_coefficientElliptic_joint_reserve_profiles` retains reserve
`Rstar - 1` in the actual full-pencil inverse and complete physical action.
`exists_normalized_elliptic_amplitude_reserve_profiles` includes the original
physical, angular and doubled radial masks, with the exact frequency factor
`ρ⁻¹`. It bounds all mixed jets at every physical position on any fixed compact
normalized full-frequency set avoiding zero, including the low radial collar.

`exists_elliptic_full_source_profiles` supplies the response consumer's exact
`L^(k - (Rstar - 2))` bound after multiplying the full amplitude by `ρ`.
It includes global smoothness and the exchanged literal adjoint, so restriction
to any of the parent's open domains inside that compact frequency set is direct.
Constants precede the varying fields, history scale, reserve and frequency.

The parent instantiates these results with the *same*
`extendedProjectedStress` and
`reducedZerothProjection ∘ extendedReducedCoefficients` from
`ResponseTransfer.RetainedFactors.exists_admissible_history_retained_coefficient_profiles`.
That producer's `HasDerivativeProfile` conclusions are exactly the two `cNorm`
premises here, at `L = currentCoefficientScale R₀ j`. The original coefficient-ball
admission, common output mask, annulus and one reference are retained. This leaf
supplies the concrete amplitude jets; the parent's diagonal phase geometry,
operator identities and same-history envelope application remain its obligations.
Source: `app:ch_regular:eq:initial-coefficient-profile`,
`app:ch_regular:eq:high-amplitude`, `app:ch_response:eq:direct-envelope-profile`.
-/
