module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.NormalBounds

/-!
# Fixed buffers for the complete retained normal

Choose the common chart for the retained full-normal restriction, its exact
scalar compatibility, and the original quadratic detector. All these choices
precede source budgets. Consumer: `NormalProfiles` for the retained adjoint
(`app:ch_background:prop:bg-adjoint`, `app:ch_waves:eq:joint-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
open ContinuumRow PhaseExtension AmplitudeProfiles LeadingPrimitive ActualCarriers FrozenMenu
open CurrentFullPhase NullTransport ActualFlow FlowAmplitude

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- A single fixed chart feeds the full-normal pullback and detector estimates.
Its graph lies in the ORIGINAL joint norm ball, while its coordinate image
lies in the producer's exact compatibility cylinder. Its doubled open ball
supplies all smoothness buffers. No current immersion, flow or scalar enters
these choices (`app:ch_waves:eq:joint-tame`, `app:ch_background:prop:bg-adjoint`). -/
theorem exists_retainedNormal_buffers {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    {σfull rcomp δcomp : ℝ} (hσfull : 0 < σfull) (hrcomp : 0 < rcomp) (hδcomp : 0 < δcomp) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      closedBall ((0 : Euclidean n), z) ρ ⊆
        ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2))
        (ball (chartCenter z) (2 * σ)) (closedBall ((0 : Euclidean n), z) ρ) ∧
      MapsTo (carrierGraph T) (ball (chartCenter z) (2 * σ))
        (ball ((0 : Euclidean n), (z, T.reference.spatialPatch z)) σfull) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2))
        (ball (chartCenter z) (2 * σ))
        (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), z) rcomp) := by
  obtain ⟨ρ, σ₀, X, V, hρ, _hσ₀, _hρle, hx, hc, hX, hV, _hXU,
    hσX, hσV, _hσK, hcoef⟩ := exists_amplitude_geometry_buffers T hP hKU hball z hz
      (by norm_num : (0 : ℝ) < 1)
  let pc := chartCenter (n := n) z
  let pf := ((0 : Euclidean n), (z, T.reference.spatialPatch z))
  let ψ := fun p : Euclidean n × CarrierParameter ↦
    coordinates (adaptedCoordinates T.data.adapted) (p.1, CanonicalCarrier.parameter p.2)
  let J := Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), z) rcomp
  have hψ : Continuous ψ := (coordinates (adaptedCoordinates T.data.adapted)).continuous.comp
    (continuous_fst.prodMk (CanonicalCarrier.parameter.continuous.comp continuous_snd))
  have hcenter : CanonicalCarrier.parameter (chartCenter (n := n) z).2 = z :=
    FullPhaseCharts.ActualComparison.carrierParameters_spectatorCenter z
  have hpc : pc ∈ X ×ˢ V :=
    ⟨hσX (mem_closedBall_self (by positivity)), hσV (mem_closedBall_self (by positivity))⟩
  have hparameter : X ×ˢ V ⊆ univ ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    fun p hp ↦ ⟨mem_univ _, (hc (hcoef hp)).2⟩
  have hg : ContinuousAt (carrierGraph T) pc :=
    (((carrierGraph_smooth T hP).mono hparameter).contDiffAt ((hX.prod hV).mem_nhds hpc)).continuousAt
  have hgraphCenter : carrierGraph T pc = pf := by
    change (0, CanonicalCarrier.parameter pc.2,
      T.reference.spatialPatch (CanonicalCarrier.parameter pc.2)) = pf
    rw [show CanonicalCarrier.parameter pc.2 = z from hcenter]
  have hcoordCenter : ψ pc = (0, ((0 : Euclidean (n - 1)), z)) := by
    change coordinates (adaptedCoordinates T.data.adapted)
      (0, CanonicalCarrier.parameter (chartCenter (n := n) z).2) = _
    rw [hcenter]
    simp
  have hψJ : ψ pc ∈ J := by
    rw [hcoordCenter]
    exact ⟨⟨by linarith, hδcomp⟩, mem_ball_self hrcomp⟩
  have hnhds : (X ×ˢ V) ∩ ((carrierGraph T) ⁻¹' ball pf σfull ∩ ψ ⁻¹' J) ∈ 𝓝 pc := by
    refine Filter.inter_mem ((hX.prod hV).mem_nhds hpc) (Filter.inter_mem ?_ ?_)
    · exact hg.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hgraphCenter]; exact mem_ball_self hσfull))
    · exact hψ.continuousAt.preimage_mem_nhds ((isOpen_Ioo.prod isOpen_ball).mem_nhds hψJ)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let σ := ε / 4
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hsmall : ball pc (2 * σ) ⊆ ball pc ε := ball_subset_ball (by dsimp [σ]; linarith)
  refine ⟨ρ, σ, hρ, hσ, hx, hc, ?_, ?_, ?_⟩
  · exact fun p hp ↦ hcoef (hsub (hsmall hp)).1
  · exact fun p hp ↦ (hsub (hsmall hp)).2.1
  · exact fun p hp ↦ (hsub (hsmall hp)).2.2

end JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
