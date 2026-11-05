module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Annulus
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualPhaseBounds
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualQuotient
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualInverses.FiniteFamily
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.FiniteFamily
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.FullBuffers
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.TransverseBuffers
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates

/-!
# Actual full-dispersion buffered phase charts

`ActualEstimates.exists_finite_actual_full_phase_charts` constructs the finite
frozen menu and the SAME current Hamilton families, then proves the conclusions
of `app:ch_seed:prop:seed-phase-charts` for each fixed incidence direction.

The output includes the actual integral scalar modulation and its nonzero
quotient identity, full and transverse global injectivity, uniform Jacobian
and inverse-differential bounds, the annular range, common open inverse targets,
and compact containment of every inner image. `modulationPhase_current_zero`
identifies the zero-epsilon value with the actual covector differential.

Both forward maps, both inverses, and all four first epsilon derivatives have
joint one-high estimates at immersion order `r+6`. The proof uses the sharp
phase order `r+3`, and derives its low budgets from primitive frame `C⁶`
closeness. All radii, thresholds, gaps, domains and high-order constants precede
the immersion. The two-sided open epsilon interval contains the closed core
and both endpoints.

Forward estimates hold on fixed integration balls containing the entire
closed physical/data cores; `full_chartBox_subset_ball` and
`transverse_chartBox_subset_ball` prove those containments. Inverse estimates
hold on the whole closure of each common target, using the existing outer
buffer to extend the SAME inverse smoothly beyond that closure. The transverse
coordinate regrouping retains time, carrier, physical, data and epsilon
variables literally.

The remaining hypotheses of this proposition are the primitive projected-stress
setup: smooth immersion, full normal rank, fixed metric/normal lower bounds,
a fixed low immersion norm, and sufficiently small frame `C⁶` distance from
the frozen frame. No phase, comparison, inverse or high-norm conclusion is an
assumed interface field. This module proves the phase-chart proposition; it
does not assert completion of Theorem 1.1.
-/
