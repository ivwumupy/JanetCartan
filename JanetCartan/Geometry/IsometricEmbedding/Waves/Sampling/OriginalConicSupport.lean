module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.IncidenceBuffers

/-!
# Original conic masks inside the retained sampling cell

Choose caps from the supplied parent cell before the original conic masks are
selected. Every smaller original carrier support lies in the parent's graph
ball, and all three literal physical cutoffs stay inside that SAME cell.
No already selected mask or continuum row is replaced.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow
open CanonicalCarrier CanonicalConic NormalizedSelection
open FullPhaseCharts.ActualComparison

/-- The original carrier and measurement masks fit the supplied compatible
parent cell at every smaller radius. This discharges the graph and cell
support inputs of `originalConic_localBalancedTransport_normal_eq_original`
when the normalized selector imposes this cap before its mask choice
(`app:ch_background:defn:bg-row`, `app:ch_waves:thm:sampling`). -/
theorem exists_originalConic_sampling_support_cap
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {ρ : ℝ} (hρ : 0 < ρ)
    {cell : Set (Euclidean n × CarrierParameter)} (hcell : IsOpen cell)
    (hcenter : ((0 : Euclidean n), (z₀ 0, spectatorCenter z₀)) ∈ cell) :
    ∃ cap > (0 : ℝ), ∀ a : ℝ, a ≤ cap →
      MapsTo (fun z ↦ (z, T.reference.spatialPatch z))
        (parameter '' carrierSupport z₀ (r := a))
        (closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4)) ∧
      ∀ b : ℝ, ∀ hb : 0 < b, b ≤ cap → ∀ i : Fin 3,
        tsupport (FixedCutoffs.physical hb i) ×ˢ carrierSupport z₀ (r := a) ⊆ cell := by
  have hzbig : z₀ ∈ parameterInterior (2 * P.radius) :=
    parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hgraph : ContinuousAt (fun z ↦ (z, T.reference.spatialPatch z)) z₀ :=
    continuousAt_id.prodMk
      ((T.reference.spatialPatch_smooth hP).continuousOn.continuousAt
        ((isOpen_parameterInterior _).mem_nhds hzbig))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hgraph.preimage_mem_nhds (ball_mem_nhds _ (by positivity : 0 < ρ / 4)))
  obtain ⟨aMax, haMax, _, hparameter⟩ :=
    exists_carrierSupport_in_parameter_ball z₀ hε zero_lt_one
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hcell.mem_nhds hcenter)
  refine ⟨min aMax (δ / 8), lt_min haMax (by positivity), ?_⟩
  intro a ha
  have haMax' : a ≤ aMax := ha.trans (min_le_left _ _)
  have haδ : a ≤ δ / 8 := ha.trans (min_le_right _ _)
  have hsupport : carrierSupport z₀ (r := a) ⊆ carrierSupport z₀ (r := aMax) := by
    intro p hp
    exact ⟨closedBall_subset_closedBall (by linarith) hp.1,
      closedBall_subset_closedBall (by linarith) hp.2⟩
  refine ⟨?_, ?_⟩
  · rintro z ⟨p, hp, rfl⟩
    exact ball_subset_closedBall (hεsub (hparameter (hsupport hp)))
  · intro b hb hbcap i p hp
    apply hδsub
    rw [← closedBall_prod_same]
    refine ⟨?_, ?_⟩
    · exact closedBall_subset_closedBall (by linarith [hbcap.trans (min_le_right _ _)])
        (FixedCutoffs.physical_tsupport_four hb i hp.1)
    · have hcarrier : p.2 ∈ closedBall (z₀ 0, spectatorCenter z₀) (a / 2) := by
        rw [← closedBall_prod_same]
        exact hp.2
      exact closedBall_subset_closedBall (by linarith) hcarrier

end JanetCartan.Sampling
