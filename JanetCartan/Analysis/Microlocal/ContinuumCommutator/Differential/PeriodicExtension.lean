module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.PeriodicExtension.Distribution

/-!
# Scalar all-data unit-torus differential commutator

For `app:ch_background:eq:bg-commutator`, the primitive joint smoothness,
physical support, low budget through `2 * (d + 1) + 1`, and high budget through
`2 * (d + 1) + (n + 1)` construct `DifferentialChart.torusSobolevCommutator` as a
continuous real-linear map from the actual periodic Hⁿ space to normalized L².

`exists_torusL2Operator_sobolev_commutator_bound` chooses the additive estimate's
constant before the amplitude, high budget, and derivative word.
`torusSobolevCommutator_ofSmooth`, `torusSobolevCommutator_unique`, and
`torusSobolevCommutator_tendsto_of_weak` prove agreement and independence.
`torusSobolevCommutator_distribution` proves the identity against every smooth
periodic test on every Hⁿ input. Its `T D^is` term is independently constructed
by actual first-order kernel transfer and the remaining actual weak derivatives;
`torusOnOrderedDerivative_ofSmooth` and `torusOnOrderedDerivative_unique` identify it.

The finite matrix/exterior assembly and geometric amplitude producers remain
with the consuming `ContinuumCommutator.Differential` task.
-/
