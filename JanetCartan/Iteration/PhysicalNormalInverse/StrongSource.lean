module

public import JanetCartan.Iteration.PhysicalSeed
public import JanetCartan.Iteration.PhysicalNormalInverse.PrescribedSource
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongSourceApplication

/-!
# Actual physical history coercivity on the single strengthened initializer

The source gap, selected conic clauses and complete history continuation below
are instantiated on `PhysicalSeed` itself.  The same literal source operator,
reference, row, masks, source cap and geometry are retained.  The stronger
initializer's arbitrary-current leading continuation is not obtained by
identifying it with a previously selected weaker tuple.

Consumer: the same-current inverse and the v2 current positive density.
-/

set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalNormalInverse
open ContinuumInverse ContinuumNormal
open ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection NormalizedCarrierProfiles
open CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase RetainedRowGeometry
open NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 RetainedFrozen
open LeadingWave LeadingWave.JointReconstruction AmbientResponse GeometricProfile
open ProjectedStressFrame WideDensity ImageGeometry ImageGeometry.Periodization

project_strong_fixed_scale_source_gap
project_strong_history_conic
apply_strong_physical_source_history_gap

end JanetCartan.PhysicalNormalInverse
