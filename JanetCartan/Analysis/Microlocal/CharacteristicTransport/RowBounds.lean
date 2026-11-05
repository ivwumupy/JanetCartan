module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.RowBounds.Profiles

/-!
# Primitive tame bounds for the literal two-time signed row

The characteristic-kernel row in `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`, is the published
`RegularSector.Characteristic.rowTransport`; its physical pullback is the
published `physicalRowTransport`. No positivity of the row is assumed.

`CharacteristicTransport.RowBounds.exists_rowTransport_cNorm_bounds` and
`CharacteristicTransport.RowBounds.exists_physicalRowTransport_cNorm_bounds`
prove additive joint bounds with reserve `μ = 0`, from fixed primitive `C¹`
budgets. Their positive constant sequences precede the coefficients, signed
datum, and inverse chart. The variable-lower-end integral and exponential
bounds are derived from the literal formulas, including both time
orientations. The graded endpoints retain `T ^ (m - R₀)` for `R₀ ≥ 1`.

The regular-sector parent retains the actual two-time Hamilton construction,
all domain and profile instantiations, and the conversion to the symbols of
`W₀`, `W₁`, and `P W₁` in
`app:ch_regular_base:eq:energy-complete-residual`. These quantitative deductions
do not assert that the unconditional sector or embedding theorem is proved.
-/
