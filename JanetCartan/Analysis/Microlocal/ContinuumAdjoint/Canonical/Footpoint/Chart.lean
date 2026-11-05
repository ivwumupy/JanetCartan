module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Transport
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Footpoint.Hamilton

/-!
# The literal canonical phase footpoint and initial section

Identify `d_ζ S` with the already constructed Hamilton coordinates and evaluate
it on the retained section. The domain follows from `PatchQuantitativeFamily`;
it is independent of the immersion. These are inputs to `Canonical.Footpoint`.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual phase footpoint equals the spatial component of the Hamilton
inverse projection chart (`app:ch_background:defn:bg-carriers`). -/
theorem transportPosition_eq_chartCoordinate {x : Euclidean n} {z : CarrierParameter}
    (h : (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z))) ∈
      (T.currentChart Q).target) :
    CanonicalCarrier.transportPosition T Q (x, z) =
      ((T.currentChart Q).coordinates
        (x, (0, T.reference.spatialPatch (CanonicalCarrier.parameter z)))).2 := by
  rw [CanonicalCarrier.transportPosition_eq_hamiltonGradient]
  exact Footpoint.gradient_zeroEnergy_phase_eq_coordinate (T.currentChart Q) h

/-- Every physical/carrier point in the full null-transport tube lies in the
Hamilton target: `LocalConstruction` supplies the physical ball and the
`3r/2` carrier interior, which is contained in the doubled closed cube.
No extra trajectory-containment premise is needed
(`app:ch_waves:thm:leading`). -/
theorem nullTransport_mem_hamiltonTarget {c C : ℝ} (hP : P.IsValid c C)
    {x : Euclidean n} {z : Euclidean 3}
    (hx : x ∈ ball 0 T.physicalRadius)
    (hz : z ∈ parameterInterior (3 * P.radius / 2)) :
    (x, (0, T.reference.spatialPatch z)) ∈ (T.currentChart Q).target := by
  exact T.target_contains_closed hx (fun i ↦ (hz i).le.trans (by linarith [hP.1]))

/-- The initial section retains its exact spatial coordinate. The source
membership is proved by the actual Hamilton producer, rather than imposed as
a new assumption on the inverse flow (`app:ch_waves:thm:leading`). -/
theorem transportPosition_on_initialSection {u : Euclidean (n - 1)}
    {z : CarrierParameter}
    (hu : T.data.adapted.embedding u ∈ ball 0 T.physicalRadius)
    (hz : CanonicalCarrier.parameter z ∈ parameterCube (2 * P.radius)) :
    CanonicalCarrier.transportPosition T Q (T.data.adapted.embedding u, z) = u := by
  have hs := T.current_section_source Q hu hz
  have ha := (T.currentChart Q).source_admissible _ hs
  have hc := (T.currentChart Q).left_inverse _ hs
  rw [(T.family.flow Q).initial_position _ ha.2, T.family.section_eq Q] at hc
  rw [transportPosition_eq_chartCoordinate T Q (T.target_contains_closed hu hz)]
  exact congrArg Prod.snd hc

end JanetCartan.ContinuumAdjoint.Canonical
