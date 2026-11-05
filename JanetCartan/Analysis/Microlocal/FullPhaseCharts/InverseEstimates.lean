module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Differential
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Epsilon
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Identifications
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.MapBounds

/-!
# Exact quotient-chart inverse estimates

Checked conditional deductions for the final paragraph of
`app:ch_seed:prop:seed-phase-charts`. `Differential` and `Epsilon` derive the
actual joint and epsilon inverse identities from the fixed inverse equation.
`FiberBounds` augments the forward map by the unchanged parameters and derives
its differential lower bound from the data gap and the forward low norm.
`LowerBound` applies the Hamilton partition identity and interpolation remainder
to obtain a one-high inverse estimate without derivative loss.

`exists_carrierQuotient_inverse_epsilon_oneHigh` assembles the
literal covector and physical integrals: the inverse and its first epsilon
derivative at joint order `r` use only primitive phase/carrier order `r+3`.
The low hypotheses are primitive `C³` bounds on fixed positive-radius balls.
All constants precede the phase, carriers and inverse. `Identifications` proves
that these formulas are the full and transverse maps used by `InverseFamily`.
No normalized data, physical, spectator or epsilon derivative is omitted.

`exists_carrierQuotient_inverse_epsilon_map_bound` transfers an explicit
primitive `r+3` budget to the map order `r+6`. The Hamilton phase/carrier
construction must supply that budget, smoothness and the integration buffers.
The inverse-family construction must supply the actual smooth inverse equation,
its common buffered containment and the fixed data-Jacobian gap. These remain
conditional analytic inputs; this module does not construct the Hamilton phase
or prove the unconditional chart-existence proposition.
-/
