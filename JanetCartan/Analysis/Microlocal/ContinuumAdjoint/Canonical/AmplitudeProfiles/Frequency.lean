module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Frequency.RadialJets

/-!
# Fixed frequency inputs for the canonical scalar-transport adjoint

`exists_fixed_angular_reserve_profiles` and
`exists_fixed_halfOrderRadialFactor_jet_bounds` produce the nonnegative fixed
profiles `P₀`, `N₀`, and `W` for
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`. They use the actual
canonical angular mask and high-frequency cutoff. The explicit angular
neighborhood is the complement of zero.

`frequencyScale_carrierChartNormalizedComponent_contDiff` supplies precisely
the amplitude field of `ModifiedNormalSymbol.PrimitiveRegularity`, from the
endpoint's primitive smoothness inputs. Their initial-scalar, flow, geometry,
and phase producers are instantiated in the parent construction.
`frequencyScale_carrierChartNormalizedComponent_support` proves the original
mask support, with compact physical/carrier/unit-direction sets and lower
radial cutoff one. The unchanged factor is literally cutoff times square root.

Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`.
-/
