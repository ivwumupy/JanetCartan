module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Phase
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalFlow
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.LocalChart
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Construction
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.BufferedConstruction
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyConstruction
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FlowJetBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ConicExtension
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameEstimates
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameBufferedFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameContinuousFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameConicFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TransverseCompatibility
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Compatibility
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.CommonFamily

/-!
# Hamilton phases

For `app:lem:common-hamilton-phase`, construct a smooth local Hamilton flow and
phase from a transverse degree-one symbol and an orthogonal initial section.
The implicit energy root, projection invertibility, smooth inverse chart, and
positive scaling law are proved. The phase satisfies the full differential,
eikonal, canonical-coordinate, and section identities.

For one symbol, the buffered construction also gives compact target closure,
a bound on the entire preimage inside the outer source ball, and a local
mixed-Hessian inverse gap. Hamilton field regularity is derived from the
scalar symbol with one derivative of loss.

For a scalar-symbol `C³` neighborhood, `exists_commonBufferedHamiltonPhases`
constructs smooth phases on common buffered targets, including explicit physical
and canonical balls and an initial-section neighborhood. It proves the phase
identities and quantitative inverse-coordinate and phase comparison bounds.
`exists_commonConicHamiltonPhases` constructs a common homogeneous extension,
with uniform mixed-Hessian and averaged-gradient gaps, canonical injectivity,
and common buffered inverse domains. `exists_commonBufferedHamiltonPhases_finiteOrder`
constructs local charts continuous from scalar-symbol `C^(m+1)` to phase `C^m`.

`exists_hamiltonPhase_cNorm_bound_from_symbol` derives the one-high inverse and
phase estimates on the same root and flow, using scalar-symbol order `m + 1`.
The root and Hamilton-field budgets are derived, rather than supplied.
`exists_commonTameHamiltonFlows` constructs the actual uniform rooted family
and proves its sharp state/projection bounds and `C¹` projection comparison.
`exists_commonTameBufferedHamiltonPhases` chooses inverse buffers inside that
same family's working ball and proves joint flow, inverse-coordinate and phase
bounds at scalar-symbol order `m + 1`, with constants before the symbol. It
retains the root cylinder, root uniqueness and initial-state identities.

`exists_commonTameConicHamiltonPhases` constructs the homogeneous extension
of the very same tame charts, with a fixed compact overlap, eikonal and
canonical-coordinate identities, flow scaling, and the sharp scalar-symbol
order `m + 1` bound. `exists_commonHomogeneousPhase_coefficient_order_three`
converts the stated scalar-symbol coefficient budget at order `k + 2` into
the explicit phase bound at coefficient order `m + 3`.

`Compatibility` proves root/ODE and inverse uniqueness and equality of phase
jets on compatible common subdomains. `TransverseCompatibility` constructs a
uniform transverse state ball, identifies initial states directly from energy
and tangential momentum, and identifies trajectories by ODE uniqueness without
exposing the chosen scalar roots. It also derives a uniform target radius
forcing inverse lifts into a prescribed source buffer.
`exists_commonTameContinuousHamiltonPhases` constructs the tame and continuous
families inside one transverse state ball, chooses common target buffers, and
identifies their coordinates by root, ODE and inverse uniqueness. Thus the same
actual local phases have sharp joint bounds and finite-order continuity. It
retains source admissibility, the projection gap, state containment and the
transverse gap for subsequent assembly.
`exists_commonTameContinuousConicHamiltonPhases` completes this assembly for
`app:lem:common-hamilton-phase`. Its conic and tame charts are identified by
root, ODE and inverse uniqueness on the prescribed normalized target radius.
The same actual family has common buffered projection and averaged-gradient
inverses, homogeneous eikonal and canonical-coordinate identities, sharp joint
flow/inverse/phase bounds at scalar-symbol order `m + 1`, and finite-order
continuity. The compact estimate box contains the middle canonical inverse
buffer. `ProjectionChart.conicPhase_cNorm_coefficient_order_three` gives the
separate coefficient-order `m + 3` phase estimate from the manuscript's scalar
symbol budget. Actual carrier-symbol instantiation belongs to the downstream
geometric constructions; this module proves the generic Hamilton phase lemma.
-/
