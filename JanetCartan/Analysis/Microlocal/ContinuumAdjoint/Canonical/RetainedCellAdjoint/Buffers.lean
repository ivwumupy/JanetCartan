module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.NormalBuffers

/-!
# Normal buffers inside an arbitrary retained carrier cell

The incidence root need not be the center of the full-leading cell. The open
carrier neighborhood is therefore retained literally. Only the auxiliary
detector chart is centered at the incidence root; neither the original scalar
norm set nor the full-normal norm set is changed.

Consumer: the retained-cell adjoint profiles for
`app:ch_background:prop:bg-adjoint` and `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
open ContinuumRow PhaseExtension AmplitudeProfiles ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Openness of the actual retained cell supplies a doubled normal buffer.
The detector ball is an auxiliary chart, not a replacement for `Kinitial` or
the retained full-normal set `J`. All choices precede the current immersion,
flows and scalar (`app:ch_background:prop:bg-adjoint`, `joint-tame`). -/
theorem exists_normal_buffers_in_retained_cell {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) (hz : z ∈ parameterCube P.radius)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hcenter : chartCenter z ∈ E) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧
      MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
        (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) ∧
      closedBall ((0 : Euclidean n), z) ρ ⊆
        ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2))
        (ball (chartCenter z) (2 * σ)) (closedBall ((0 : Euclidean n), z) ρ) ∧
      ball (chartCenter z) (2 * σ) ⊆ E := by
  obtain ⟨ρ, σ₀, X, V, hρ, hσ₀, _hρle, hx, hc, hX, hV, _hXU,
    hσX, hσV, _hσK, hcoef⟩ := exists_amplitude_geometry_buffers T hP hKU hball z hz
      (by norm_num : (0 : ℝ) < 1)
  have hpc : chartCenter (n := n) z ∈ X ×ˢ V :=
    ⟨hσX (mem_closedBall_self hσ₀.le), hσV (mem_closedBall_self hσ₀.le)⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (((hX.prod hV).inter hE).mem_nhds ⟨hpc, hcenter⟩)
  have hsmall : ball (chartCenter (n := n) z) (2 * (ε / 4)) ⊆
      ball (chartCenter z) ε := ball_subset_ball (by linarith)
  exact ⟨ρ, ε / 4, hρ, by positivity, hx, hc,
    fun _ hp ↦ hcoef (hsub (hsmall hp)).1,
    fun _ hp ↦ (hsub (hsmall hp)).2⟩

end JanetCartan.ContinuumAdjoint.Canonical.RetainedCellAdjoint
