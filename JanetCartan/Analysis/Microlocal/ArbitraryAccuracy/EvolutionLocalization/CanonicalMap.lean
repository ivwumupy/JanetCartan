module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation

/-!
# The actual canonical map used by elapsed graph localization

The map is the energy-preserving lift of the original root flow. Its forward
relation is proved from the inverse two-time chart, including the source base
and every temporal covector. These are geometric inputs to the chart-control
and buffered-localizer constructions for `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The canonical map of the literal fixed-elapsed-time graph, at arbitrary
input energy. Consumer: both chart orientations and the common image buffer
in `app:ch_regular:lem:finite-chain`. -/
def elapsedCanonicalMap (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    Euclidean (d + 1) × Euclidean (d + 1) :=
  rootSuspensionState h (rootSuspension h p) (Φ (spacetimeRootState p, r))

/-- Projecting the actual map recovers the original root flow
(`app:ch_regular:eq:joint-stationary`). -/
@[simp] theorem spacetimeRootState_elapsedCanonicalMap
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    spacetimeRootState (elapsedCanonicalMap h Φ r p) = Φ (spacetimeRootState p, r) :=
  spacetimeRootState_rootSuspensionState _ _ _

/-- Energy preservation of the actual map holds at every input temporal
covector; it does not assert zero energy (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem rootSuspension_elapsedCanonicalMap
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    rootSuspension h (elapsedCanonicalMap h Φ r p) = rootSuspension h p :=
  rootSuspension_rootSuspensionState _ _ _

/-- The two-time projection of the source point is exactly the chart point
of the lifted map. The clock hypothesis is the conclusion of
`exists_localTwoTimeHamiltonPhase` (`app:ch_regular:eq:joint-stationary`). -/
theorem elapsedChartPoint_elapsedCanonicalMap
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1))
    (hclock : (Φ (spacetimeRootState p, r)).1 = p.1 0 + r) :
    elapsedChartPoint r (elapsedCanonicalMap h Φ r p).1 p.2 =
      twoTimeProjection Φ (p.1 0 + r, spacetimeRootState p) := by
  simp only [elapsedChartPoint, elapsedCanonicalMap, rootSuspensionState,
    timeSpacePoint_time, spatialPart_timeSpacePoint, twoTimeProjection, twoTimeState]
  change ((Φ (spacetimeRootState p, r)).1,
    ((Φ (spacetimeRootState p, r)).1 - r,
      ((Φ (spacetimeRootState p, r)).2.1, spatialPart p.2))) =
    (p.1 0 + r, (p.1 0,
      ((Φ (spacetimeRootState p, p.1 0 + r - p.1 0)).2.1, spatialPart p.2)))
  simp only [add_sub_cancel_left, hclock, add_sub_cancel_right]

/-- The actual lifted flow lies on the literal elapsed canonical relation.
Every premise is a coordinate, clock, or differential output of the two-time
phase constructor, restricted to its actual source. Consumer: the `relation`
field of the forward chart control (`app:ch_regular:eq:joint-stationary`). -/
theorem forwardRelation_elapsedCanonicalMap
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (r : ℝ) (p : Euclidean (d + 1) × Euclidean (d + 1))
    (hsource : (p.1 0 + r, spacetimeRootState p) ∈ C.source)
    (hclock : (Φ (spacetimeRootState p, r)).1 = p.1 0 + r)
    (hphase : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) :
    FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r)
      p.1 p.2 (elapsedCanonicalMap h Φ r p).1 (elapsedCanonicalMap h Φ r p).2 := by
  have he := elapsedChartPoint_elapsedCanonicalMap h Φ r p hclock
  rw [← hC] at he
  have ht := he ▸ C.map_source hsource
  have hi : C.symm (elapsedChartPoint r (elapsedCanonicalMap h Φ r p).1 p.2) =
      (p.1 0 + r, spacetimeRootState p) := by
    rw [he, C.left_inv hsource]
  apply (forwardRelation_elapsedChartPhase_iff (hphase _ ht)).mpr
  constructor
  · unfold elapsedInputBase
    rw [hi]
    change p.1 = timeSpacePoint ((Φ (spacetimeRootState p, r)).1 - r) (spatialPart p.1)
    rw [hclock, add_sub_cancel_right, timeSpacePoint_coordinates]
  · simp only [elapsedOutputCovector, hi, twoTimeState]
    simp only [elapsedChartPoint, elapsedCanonicalMap, rootSuspensionState,
      timeSpacePoint_time, spatialPart_timeSpacePoint]
    change timeSpacePoint (p.2 0 - h (spacetimeRootState p) +
      h (Φ (spacetimeRootState p, r))) (Φ (spacetimeRootState p, r)).2.2 =
      timeSpacePoint (p.2 0 +
        h ((Φ (spacetimeRootState p, r)).1,
          ((Φ (spacetimeRootState p, r)).2.1,
            (Φ (spacetimeRootState p, p.1 0 + r - p.1 0)).2.2)) -
        h ((Φ (spacetimeRootState p, r)).1 - r, (spatialPart p.1, spatialPart p.2)))
        (Φ (spacetimeRootState p, p.1 0 + r - p.1 0)).2.2
    simp only [add_sub_cancel_left, Prod.eta]
    rw [hclock, add_sub_cancel_right]
    congr 1
    change p.2 0 - h (spacetimeRootState p) + h (Φ (spacetimeRootState p, r)) =
      p.2 0 + h (Φ (spacetimeRootState p, r)) - h (spacetimeRootState p)
    ring

/-- Every point of the literal elapsed relation is the same actual lifted
flow value. This direction uses target membership, so it also identifies
complementary kernel supports (`app:ch_regular:lem:finite-chain`). -/
theorem elapsedCanonicalMap_eq_of_forwardRelation
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hq : elapsedChartPoint r q.1 p.2 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r q.1 p.2))).1 = q.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r q.1 p.2))
      (elapsedChartPoint r q.1 p.2))
    (hrel : FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r)
      p.1 p.2 q.1 q.2) :
    elapsedCanonicalMap h Φ r p = q :=
  (forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel).1.symm

/-- Smoothness of the lifted map is inherited from the original root and
flow, at their actual input and output points. No regularity at spatial
covector zero is asserted. Consumer: compact common elapsed image carriers
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiffAt_elapsedCanonicalMap
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {r : ℝ} {p : Euclidean (d + 1) × Euclidean (d + 1)}
    (hi : ContDiffAt ℝ ∞ h (spacetimeRootState p))
    (ho : ContDiffAt ℝ ∞ h (Φ (spacetimeRootState p, r)))
    (hΦ : ContDiffAt ℝ ∞ Φ (spacetimeRootState p, r)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
      elapsedCanonicalMap h Φ z.1 z.2) (r, p) := by
  have ht : ContDiff ℝ ∞ (fun x : Euclidean (d + 1) => x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff
  have hw : ContDiff ℝ ∞ (spacetimeRootState (d := d)) :=
    (ht.comp contDiff_fst).prodMk
      ((spatialPartCLM.contDiff.comp contDiff_fst).prodMk
        (spatialPartCLM.contDiff.comp contDiff_snd))
  have hw' : ContDiff ℝ ∞ (fun z : ℝ × (Euclidean (d + 1) × Euclidean (d + 1)) =>
      spacetimeRootState z.2) := hw.comp contDiff_snd
  have hf := hΦ.comp (r, p) (hw'.contDiffAt.prodMk contDiffAt_fst)
  have he := (ht.comp (contDiff_snd.comp contDiff_snd)).contDiffAt.sub
    (hi.comp (r, p) hw'.contDiffAt)
  exact (timeSpacePointCLM.contDiff.contDiffAt.comp (r, p)
    (hf.fst.prodMk hf.snd.fst)).prodMk
      (timeSpacePointCLM.contDiff.contDiffAt.comp (r, p)
        ((he.add (ho.comp (r, p) hf)).prodMk hf.snd.snd))

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
