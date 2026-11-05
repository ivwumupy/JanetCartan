module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FlowBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph

/-!
# Common buffers for the leading wave and supported carrier

The fixed graph, compatible flow cylinder, detector ball and Hamilton domain
have a common neighborhood of the frozen incidence point. This supplies the
geometric inputs of `LeadingPrimitive.exists_primitive_controls_of_jointLeading`
and the open set in `UniformConic` for the SAME local leading family.
Sources: `app:ch_background:eq:bg-mixed-input`, `bg-T`, and
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumRow.LeadingCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open CanonicalCarrier LeadingPrimitive
open FullPhaseCharts FullPhaseCharts.ActualComparison

/-- Choose the carrier coefficient neighborhood inside the retained leading
graph and compatibility buffers, before all geometric and scalar budgets.
The entire open neighborhood, not just the compact norm chart, has these
containments (`app:ch_background:eq:bg-mixed-input`, `bg-T`). -/
theorem exists_leading_carrier_buffers {n : ℕ} {P : Patch n} {c C : ℝ}
    (hP : P.IsValid c C) {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {K : Set (Euclidean n)}
    (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    {σ rcomp δcomp : ℝ} (hσ : 0 < σ) (hrcomp : 0 < rcomp) (hδcomp : 0 < δcomp) :
    ∃ ε > (0 : ℝ), ∃ ρdet > (0 : ℝ),
      let E := ball (0 : Euclidean n) ε ×ˢ ball (z 0, spectatorCenter z) ε
      let a := ((0 : Euclidean n), (z, T.reference.spatialPatch z))
      let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2)
      MapsTo (carrierGraph T) E (ball a σ) ∧
      MapsTo (fun p ↦ coordinates (adaptedCoordinates T.data.adapted) (ψ p)) E
        (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), z) rcomp) ∧
      E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
        (parameter ⁻¹' parameterInterior (2 * P.radius)) ∧
      E ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρdet)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      closedBall ((0 : Euclidean n), z) ρdet ⊆
        ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
      MapsTo ψ E (closedBall ((0 : Euclidean n), z) ρdet) := by
  obtain ⟨ε₀, hε₀, ρdet, hρdet, _, hXU, hfield, _, hcomp, hphase,
    hxdet, hdet, hmaps⟩ := exists_canonical_flow_buffers hP T hKU hball z hz
      (R := 32 * rcomp) (τ := δcomp) (by positivity) hδcomp
  let p : Euclidean n × CarrierParameter := (0, (z 0, spectatorCenter z))
  have hz2 : z ∈ parameterInterior (2 * P.radius) := fun i ↦
    (hz i).trans_lt (by linarith [hP.1])
  have hp : p ∈ univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    refine ⟨mem_univ _, ?_⟩
    simpa only [p, mem_preimage, parameter_apply, carrierParameters_spectatorCenter] using hz2
  have hopen : IsOpen (univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius)) :
      Set (Euclidean n × CarrierParameter)) :=
    isOpen_univ.prod ((isOpen_parameterInterior _).preimage parameter.continuous)
  have hgraph : ContinuousAt (carrierGraph T) p :=
    (carrierGraph_smooth T hP).continuousOn.continuousAt (hopen.mem_nhds hp)
  have hcenter : carrierGraph T p = (0, (z, T.reference.spatialPatch z)) := by
    simp only [carrierGraph, p, parameter_apply, carrierParameters_spectatorCenter]
  obtain ⟨ε₁, hε₁, hε₁graph⟩ := Metric.eventually_nhds_iff_ball.mp
    (hgraph.preimage_mem_nhds (ball_mem_nhds (carrierGraph T p) hσ))
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hsub : ball (0 : Euclidean n) ε ×ˢ ball (z 0, spectatorCenter z) ε ⊆
      ball (0 : Euclidean n) ε₀ ×ˢ ball (z 0, spectatorCenter z) ε₀ :=
    prod_mono (ball_subset_ball (min_le_left _ _)) (ball_subset_ball (min_le_left _ _))
  refine ⟨ε, hε, ρdet, hρdet, ?_, ?_, ?_, hsub.trans hphase, hxdet, hdet,
    fun q hq ↦ hmaps (hsub hq)⟩
  · intro q hq
    have hqp : q ∈ ball p ε₁ := by
      apply ball_subset_ball (min_le_right ε₀ ε₁)
      simpa only [p, ball_prod_same] using hq
    simpa only [hcenter] using hε₁graph q hqp
  · intro q hq
    simpa only [show 32 * rcomp / 32 = rcomp by ring] using hcomp (hsub hq)
  · intro q hq
    exact ⟨⟨hXU (hsub hq).1, (hfield (hsub hq)).1⟩, (hfield (hsub hq)).2⟩

end JanetCartan.ContinuumRow.LeadingCarrier
