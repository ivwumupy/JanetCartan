module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Jets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Denominator
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Roots

/-!
# Incidence coefficient and root budgets

Checked conditional deductions for Step 3 of
`app:ch_seed:prop:seed-actual-menu` and `app:ch_seed:eq:seed-phase-tame`.

* `exists_cNorm_incidence_le_primitive` derives the literal incidence seminorm
  from separate frame, phase-gradient and testing-covector seminorms.
* `exists_incidence_jet_profile` supplies the equation profile for the existing
  transverse implicit-root recurrence.
* `scalarDerivative_incidence_eq` and `exists_incidence_denominator_radius`
  derive the transverse denominator and reciprocal budget from compact frozen
  primitive first jets, their gap, and actual first-jet closeness.
* `exists_cNorm_incidence_root_le_reserve_six` gives the root bound with exactly
  the paper's `r + 6` reserve from frame loss two and phase-gradient loss four.

The consumer `jc-actual-carriers` must instantiate the primitive estimates from
`jc-projected-stress-frame` and `jc-hamilton-phase`, the fixed compact covector
patch and low bounds, and the supplied smooth interior roots and transverse
gaps from `jc-carrier-continued-incidence`. The implicit jet recurrence is the
checked `CharacteristicRoot` API. This module constructs neither the phases nor
the roots, and asserts no unconditional carrier existence theorem.
-/
