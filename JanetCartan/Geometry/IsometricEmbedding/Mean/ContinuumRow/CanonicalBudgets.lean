module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Detector
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NullAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.NormalField
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Assembly

/-!
# Primitive budgets for the canonical continuum carrier

`CanonicalCarrier.exists_canonical_primitive_controls` discharges the primitive
norm and finite-kernel premises of the released global carrier constructor for
the literal `CanonicalCarrier.data`. It uses the SAME projected stress, Hamilton
chart, scalar amplitude, null column, and retained local-flow maps.

The additive high budget has fixed reserve fourteen. Fixed primitive C15
immersion and initial-data bounds supply the low norms. The theorem includes
all five `CoefficientNormCharts.Controls` fields, the transported-position
order `s + 2` estimate, strong measurability of the zero-extended kernel, and
its exact square-root frequency amplitude bound. Fixed mask contributions are
derived from their actual compact norms.

Sources: `app:ch_background:eq:bg-mixed-input`, `bg-T`,
`bg-full-complex-amplitude`, and `app:ch_waves:eq:joint-tame`.

The coefficient/flow inputs are the proved outputs of
`NullTransport.exists_projected_local_positive_amplitude`. The parent retains
instantiation with its chosen history, conic domains and supported masks,
finite-family assembly, and application of the global operator theorem. This
module does not assert the unconditional continuum-row existence theorem.
-/
