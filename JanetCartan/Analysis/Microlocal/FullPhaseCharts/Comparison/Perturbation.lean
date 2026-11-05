module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Transverse

/-!
# Quantitative perturbation of the literal phase charts

For the comparison following `app:ch_seed:eq:seed-quotient-integral`:

* `exists_modulationChart_perturbation_bound` controls the literal averaged
  physical gradient and its full joint derivative;
* `exists_fullChart_perturbation_bound` controls full-chart values, actual
  joint derivatives in `(p,x,x',z,η)`, and actual `(z,η)` data derivatives;
* `exists_transverseChart_perturbation_bound` controls transverse values and
  actual `η` derivatives at common-time endpoints.

Each positive constant is selected from fixed compact geometry and the smooth
carrier before choosing either phase. The bound is `C * cNorm K 4 (S - S₀)`.
Local phase smoothness on the open phase domain, compact shifted-segment
containment, and explicit open geometric buffers suffice, including at zero
shift. The literal quotient identity, differentiation of both integrals,
phase-jet bounds, and transverse projection identity are proved in the imported
leaf modules. No quotient or chart-error bound is assumed.

The consumer `jc-deduce-full-phase-jet-comparison` must instantiate the geometric
buffers and combine these estimates with the separate reference comparison.
These perturbation results do not assert smallness of the reference epsilon
derivative or construct a Hamilton phase.
-/
