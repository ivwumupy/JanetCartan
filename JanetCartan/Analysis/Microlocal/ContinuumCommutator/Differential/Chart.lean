module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Bounds

/-!
# Unit-torus charts for full-amplitude differential commutators

For `app:ch_background:eq:bg-commutator`, this module supplies the actual chart
transfer for amplitudes supported in both physical positions in a fixed box
of radius less than `1/2`:

* exact normalized-Haar/Lebesgue kernel comparison and bounded realization;
* construction and independence of a fixed compact smooth source extension;
* cancellation of artificial extension derivatives on the source support;
* output localization, literal adjoint transport, and exact output L² norms;
* the ordered periodic weak commutator identity on smooth periodic inputs;
* the local Hⁿ comparison, with constants depending only on the fixed cutoff;
* scalar and finite-matrix additive periodic Hⁿ/L² commutator estimates.

The final estimates are `exists_torusL2Operator_periodic_commutator_bound` and
`exists_matrixTorusL2Operator_periodic_commutator_bound`, in namespace
`JanetCartan.Pseudodifferential.DifferentialChart`. They retain the full physical
amplitude, its low and high derivative budgets, and the literal `2π` convention.
The parent construction must instantiate these hypotheses for its actual normal
amplitudes and perform its all-data extension.
-/
