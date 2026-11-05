module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Construction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity

/-!
# Protected masks for the direct residual relations

For `app:ch_regular:lem:finite-chain`, `exists_nested_canonicalDirectLocalizers`
constructs finite nested masks from the actual common root flows, compact
initial/whole-segment buffers and the SAME retained comparison geometry.
Relation compactness, physical angular protection and canonical pullbacks are
proved internally. Every closed input shoulder maps through the full diagonal
and both actual zero-energy orientations into the next open plateau. The source
buffer, annular supports, depth zero and original elapsed bound are retained.
`sourceRecutRelation_mem_nested_plateau` keeps the literal source recut over
`tsupport χ₂`, where `χ₃ = 1`.

`compact_canonicalElapsedFamily_stationary_exclusions` supplies the exact
interior and boundary exclusions on the full finite total carrier, including
both external bases and the complementary output support. Its primitive
inverse-chart, phase-differential and whole-segment hypotheses must be checked
on the actual factor rectangles from `UniformGeometry`.

`exists_uniform_conic_nested_localization_data` assembles the coefficient-
uniform result for each fixed depth. Common positive shoulders, lower and upper
frequency bounds, all-order mask derivative bounds, interior gaps, boundary
collars and cutoff derivative bounds precede the current coefficient field
and requested accuracy. Its canonical masks are the literal
`canonicalProofLocalizer` pullbacks; angular protection is imposed in physical
coordinates. A finite radial proof cover uses the SAME homogeneous roots,
flows, inverse charts and physical factors. The original elapsed interval,
both orientations and full diagonal branches are preserved.

The full-gradient exclusions and boundary tangential exclusions at elapsed
time zero are conclusions of that construction, for both the conic phase and
its constructed supported extension. They hold on the entire closed input
shoulder and output complement, with arbitrary external bases, as required by
`GradientGaps` and `UniformCollar`. No compactness of a varying coefficient
class is used. Source recutting retains `χ₃ = 1` on `tsupport χ₂`.

The arbitrary-accuracy parent still instantiates the following primitive
inputs on its actual finite current family; no mask or gradient gap remains
among these inputs:

* The compact source `S`, its open prescribed buffer `V`, and a common compact
  physical envelope `B` inside `ball 0 (2*r)`, with nonzero source covectors
  whose normalized directions lie in `interior Ω` and `Ω ⊆ interior Γin`.
* The SAME smooth pencil `Q` with `cNorm (closedBall 0 (2*r)) 3 Q ≤ M`;
  selected root sections, centers and transverse/root-value bounds; the open
  radially invariant root domains and common normalized root-speed gap.
  `UniformGeometry.exists_uniform_fieldRoot_conicGeometry` supplies these
  root controls, as extracted by `ConicInterior.fieldRoot_maskAssembly_primitives`
  and `ConicInterior.fieldRoot_maskAssembly_radial_invariance`.
* That constructor's `IsSmoothFlowOn` with radii `3*ρ` and `3*ρ/2`, inverse
  two-time chart with source radius `σ` and target buffer `2*β`, its exact
  phase differential, diagonal identity and WHOLE inverse-segment controls.
  The order-two flow/inverse/phase sum is bounded by `Bphase*(1+C³(Q))`.
  The selected buffers obey `0 < γ ≤ min β σ`; the original elapsed bound
  satisfies `0 ≤ Δ < T`. Localization uses the supported domain `r' ≤ γ`
  within `Icc 0 Δ`, without changing `Δ` with depth.
* Closed physical segment buffers and the literal physical factor masks,
  together with the SAME retained comparison charts and source cover from
  `ProtectedFlow.exists_initialized_signed_no_return_with_graph_bounds`.
  Its common positive gradient norm bounds, derivative bound and angular
  buffer supply the protection inputs. Signed charts are retained in the
  finite index, and the original source cutoffs supply `EqOn χ₃ 1 (tsupport χ₂)`.

This completes the protected-mask deduction for
`finiteChain_observation_rapidDecayAt`; selecting those actual charts and
instantiating their domain restrictions is a separate parent obligation.
-/
