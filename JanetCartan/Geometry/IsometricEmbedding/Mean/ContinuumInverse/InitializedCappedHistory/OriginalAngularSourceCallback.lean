module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary
public import JanetCartan.Iteration.PhysicalSeed.AngularRaw
public meta import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalAngularSourceCallback.Construction

/-!
# The stronger source-row callback on the already chosen original Mean reference

Apply AngularRaw to the same original H, seed, candidate cells and arbitrary
original21 inputs. The angular bound is added at the end of the existing prefix,
without changing the old source/raw/inverse/target-gap clauses. This module does
not choose any row. The later SelectedBoundary must select once from this
stronger existential, before the source operator, scalar profiles and common f
are chosen (`new:sec:order-of-choices`, `app:ch_background:defn:bg-row`,
`new:eq:amplitude-test`).

Only that late boundary may import this module. Importing it in the original
initializer's early extraction module would create a reference/initializer cycle.
No independently cached PhysicalSeed reference or selected source is imported.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
open JanetCartan
open ContinuumInverse.InitializedCappedHistory
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction

apply_original_angular_source_callback
