module

public import JanetCartan.Analysis.ODE.SmoothDependence.LocalExistence
public import JanetCartan.Analysis.ODE.SmoothDependence.Parameters
public import JanetCartan.Analysis.ODE.SmoothDependence.Variational
public import JanetCartan.Analysis.ODE.SmoothDependence.DifferentiableFlow
public import JanetCartan.Analysis.ODE.SmoothDependence.DifferentiableParameters
public import JanetCartan.Analysis.ODE.SmoothDependence.HigherRegularity
public import JanetCartan.Analysis.ODE.SmoothDependence.SmoothFlow
public import JanetCartan.Analysis.ODE.SmoothDependence.SmoothParameters

/-!
# Smooth dependence of local ODE solutions

Analytic foundations for `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` in `paper.tex`.

The main existence theorems are `JanetCartan.ODE.exists_contDiffOn_localFlow_in_open`
and `JanetCartan.ODE.exists_contDiffOn_parameterized_localFlow_in_open`. For any
finite order `n ≥ 1`, or `n = ∞`, they construct jointly `Cⁿ` local flows on
bounded open product domains. The same flows are continuous and uniformly
Lipschitz in their initial data and parameters on the closed domains, with a
prescribed open range buffer. Their actual derivatives satisfy the initial-data
and parameter variational equations on the entire open time interval.

The first derivative is proved using the Taylor remainder and Grönwall.
Higher orders follow by applying linear-evolution regularity to that derivative
and inducting, preserving one common domain at all orders. All inputs to this
construction are discharged from Picard–Lindelöf. Quantitative higher-derivative
budgets and the Hamilton phase construction are separate results.
-/
