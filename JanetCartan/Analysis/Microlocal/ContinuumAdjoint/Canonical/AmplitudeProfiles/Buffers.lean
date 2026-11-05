module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.LocalConstruction

/-!
# Fixed geometric buffers for the amplitude profiles

The retained coefficient ball need not itself lie in the phase domain. We
restrict its nullvector estimates to a smaller ball, chosen before the current
immersion. This supplies every geometric containment of the `C₀` producer
for `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow PhaseExtension ActualCarriers FrozenMenu CurrentFullPhase
open NullTransport FullPhaseCharts FullPhaseCharts.ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Restrict the actual coefficient ball and choose a fixed open product chart
containing the geometric cutoff. Only the primitive patch and the producer's
positive coefficient radius enter. Consumer:
`exists_carrierChartGeometryComponent_profiles` (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_amplitude_geometry_buffers {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ρg σ : ℝ, ∃ X : Set (Euclidean n), ∃ V : Set CarrierParameter,
      0 < ρg ∧ 0 < σ ∧
      closedBall ((0 : Euclidean n), z) ρg ⊆ closedBall ((0 : Euclidean n), z) ρ ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρg)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      closedBall ((0 : Euclidean n), z) ρg ⊆
        ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
      IsOpen X ∧ IsOpen V ∧ X ⊆ U ∧
      closedBall (0 : Euclidean n) σ ⊆ X ∧
      closedBall (chartCenter (n := n) z).2 σ ⊆ V ∧
      closedBall (0 : Euclidean n) σ ⊆ K ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
        (closedBall ((0 : Euclidean n), z) ρg) := by
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ×ˢ
    parameterInterior (2 * P.radius)) ∩ ball ((0 : Euclidean n), z) ρ
  have hΩ : IsOpen Ω := (isOpen_ball.prod (isOpen_parameterInterior _)).inter isOpen_ball
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω :=
    ⟨⟨mem_ball_self T.physicalRadius_pos,
      fun i ↦ (hz i).trans_lt (by linarith [hP.1])⟩, mem_ball_self hρ⟩
  obtain ⟨ρg, _, hρg, _, hg, hx, _⟩ := exists_adapted_coefficient_ball T hΩ z hzΩ
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  have hψ : Continuous ψ :=
    continuous_fst.prodMk (CanonicalCarrier.parameter.continuous.comp continuous_snd)
  have hcenter : ψ (chartCenter (n := n) z) = (0, z) := by
    change (0, carrierParameters (spectatorCenter z, z 0)) = (0, z)
    rw [carrierParameters_spectatorCenter]
  have hc : chartCenter (n := n) z ∈ ψ ⁻¹' ball ((0 : Euclidean n), z) ρg := by
    change ψ (chartCenter (n := n) z) ∈ ball ((0 : Euclidean n), z) ρg
    rw [hcenter]
    exact mem_ball_self hρg
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp ((isOpen_ball.preimage hψ).mem_nhds hc)
  let X := ball (0 : Euclidean n) δ
  let V := ball (chartCenter (n := n) z).2 δ
  have hcoef : MapsTo ψ (X ×ˢ V) (closedBall ((0 : Euclidean n), z) ρg) := by
    intro p hp
    have hpball : p ∈ ball (chartCenter (n := n) z) δ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact hp
    exact ball_subset_closedBall (hd hpball)
  have hXK : X ⊆ K := by
    intro x hxX
    have hp : (x, (chartCenter (n := n) z).2) ∈ X ×ˢ V :=
      ⟨hxX, mem_ball_self hδ⟩
    have hm := hcoef hp
    have hxball := hx hm
    exact hball hxball
  have hσX : closedBall (0 : Euclidean n) (δ / 2) ⊆ X :=
    closedBall_subset_ball (half_lt_self hδ)
  exact ⟨ρg, δ / 2, X, V, hρg, half_pos hδ,
    fun p hp ↦ ball_subset_closedBall (hg hp).2, hx,
    fun p hp ↦ (hg hp).1, isOpen_ball, isOpen_ball, hXK.trans hKU,
    hσX, closedBall_subset_ball (half_lt_self hδ), hσX.trans hXK, hcoef⟩

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
