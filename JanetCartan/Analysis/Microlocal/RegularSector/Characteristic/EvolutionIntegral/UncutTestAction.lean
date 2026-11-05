module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.ReverseLimit
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FinitePrimitive

/-!
# The original uncut fixed-time and retarded test actions

For `app:ch_regular_base:eq:fixed-time-representation`, the actual uncut
multiplier is the function-valued inverse Fourier transform, with the exact
physical-to-cycle factor. Only `d+2` bounded symbol derivatives are needed:
Leibniz bounds and the original Schwartz test give integrable frequency jets;
finite-regularity Fourier decay gives integrability on every spatial slice.
The temporal integral is continuous and integrable from the zeroth-order
bound. Pointwise Fourier inversion and Fubini therefore identify the original
spatial graph without claiming Schwartz regularity from finite budgets.

Dominated convergence removes the cutoff at fixed elapsed time and on the
elapsed slab. The lower buffer preserves the original endpoints and turns
that slab into the literal retarded interval. The exact strong-limit and
cutoff-preservation conclusions of `PrimitiveRetarded` thus identify its SAME
bounded operators with `Mχout U_b Bβ Mχsource` and `Mχout E_b Bβ Mχsource`.
`retardedOperator_eq_uncutPhysicalIntegral_of_primitive_budgets` discharges
all new derivative and amplitude bounds from the parent's original finite
reserve and joint carrier cover, including the empty-mask cases.

The checked literal reversed-triangle test pairing identifies the actual
Hilbert adjoint, retaining `Mχsource* Bβ* E_b* Mχout*`, both masks, physical
normalization, lower buffer and endpoints. It uses only finite zeroth-order
bounds. The previous Schwartz-valued variants are retained, with their
explicit all-order hypothesis; the finite-budget path does not use it.

Final instantiation of the constructed operator and the full integer Sobolev
estimate remain with the parent. No uncut action, convergence to that action,
operator-norm continuity or integrated Sobolev estimate is an input here.
-/
