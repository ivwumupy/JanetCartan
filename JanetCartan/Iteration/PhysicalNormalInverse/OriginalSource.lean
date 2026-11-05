module

public import JanetCartan.Iteration.PhysicalNormalInverse.PrescribedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCappedHistory.OriginalHistoryGap.Conic
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalSourceApplication

/-!
# Actual original-source coercivity for physical Schwartz histories

Apply every argument of the physical prescribed-source construction to the
identical original 21 initializer parameters and the actual
`OriginalSourceGap.source_input`, at the original scale `σ ∈ Ioc 0 sourceCap`.
The only additional inputs are the fixed physical band constant `Bband ≥ 1`,
`rStar ≥ canonicalCarrierLowOrder n`, and the literal revised minimal-order
inequality.  No source gap, current gap, coefficient success or new row is an
additional hypothesis.

The generated ordinary kernel-checked declarations in
`PhysicalNormalInverse.OriginalSource` retain `Sgap`, `coeffHistory`, their
formula/smoothness certificates, and the complete current-carrier/half-gap
continuation.  `source_continuation` fixes the source operator to the SAME
`OriginalSourceGap.Vop`, not merely an operator with a new choice of row.

The maps remain `RevisedGlobal.finiteMap (sourceDilation H.map σ) history`, with
global Schwartz increments and radian Fourier budgets.  The parent must still
instantiate the original 21 callbacks with the shared revised initializer and
feed this exact operator into the fixed-source inverse/mean construction.
This does not assert completion of Main.
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

apply_original_physical_source_history_gap

end JanetCartan.PhysicalNormalInverse
