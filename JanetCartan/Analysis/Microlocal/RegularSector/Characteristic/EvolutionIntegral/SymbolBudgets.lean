module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.HighBound
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.LowAmplitude
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.LowPhase

/-!
# Primitive symbol budgets for the actual elapsed graph

This module proves the analytic symbol-budget deductions for
`app:ch_regular_base:lem:retarded-kernel`, using exactly `Basic.elapsedPhase`
and `Basic.elapsedAmplitude` from
`app:ch_regular_base:eq:fixed-time-representation`.

* `exists_elapsed_graph_high_constant` bounds the actual
  `normalizedGraphOrderHigh` by a fixed constant times one plus the original
  joint amplitude and phase seminorms. It treats both symbol orders and is
  uniform for `r∈[0,Δ]`. The pullback loses zero derivatives, so the integer
  consumer's shift `μ₀+2` is unchanged.
* `elapsedAmplitude_normalizedSeminorm_le` and
  `elapsedAmplitude_orderMinusOneSeminorm_le` construct the exact profile
  finiteness and bounds used by `PrimitiveProfiles` and `GainOneProfiles`.
* `exists_elapsed_fullLowReserve_constant` supplies
  `HasFullSourceSymbolBound` at `fullLowReserve (d+1)`, from the original
  primitive low bound and a fixed normalized carrier cover.
* `wholeImagePhaseReserve_elapsedPhase` supplies the literal normalized
  dyadic-shell phase jets required by `PrimitiveRealization.Family`.
* `spatial_annulus_of_normalized_multiplier_cone` proves why a spatial
  order-minus-one symbol has full spacetime order minus one on the fixed
  multiplier cone. The same frequency comparison holds for every nonzero
  differentiated amplitude. Both physical masks, both positions and the
  lower-time buffer remain inside the actual differentiated fields.

All matrix norms are Frobenius norms. The constants contain only fixed chart,
mask, multiplier, slab and order data. No elapsed seminorm estimate, inverse
estimate or operator norm is an input.

The separate geometric construction supplies the fixed normalized buffered
chart inclusions and carrier cover. The original phase and transport-symbol
producers supply their actual joint smoothness, symbol-class finiteness,
low-frequency support and low bounds. The parent retains the graph constructor,
integer Sobolev estimates and time integration. These deductions do not assert
unconditional existence of the retarded operator or its geometric charts.
-/
