module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.IncidenceBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FrozenDetectorBuffer

/-!
# Original incidence domains for every retained detector submask

Choose spatial and angular caps from the original frozen chart before any
conic or finite incidence selection. Every later submask has its full closed
carrier/detector support in that same original incidence domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open FullPhaseCharts FullPhaseCharts.ActualComparison

/-- Convert the original frozen detector buffer into caps for the actual
spatial and angular masks. The entire closed support survives any smaller
mask choice and the quarter-sphere rescaling of its central covector.
Consumers are the common finite selector and
`Sampling.transverseDetectorIncidenceSupport_spec`
(`app:ch_background:defn:bg-row`, `app:ch_waves:thm:sampling`). -/
theorem exists_incidence_detector_submask_caps
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    {O : Set (Euclidean n)} (hO : IsOpen O) (hkO : NormedSpace.normalize k ∈ O) :
    ∃ aMax bMax : ℝ, 0 < aMax ∧ 0 < bMax ∧
      ∀ (a r : ℝ) (η : Euclidean (n - 1)), a ≤ aMax →
        NormedSpace.normalize η = NormedSpace.normalize
          (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) →
        angularWidth η r ≤ bMax →
        MapsTo parameter (carrierSupport z₀ (r := a)) (parameterInterior P.radius) ∧
        (∀ z ∈ parameter '' carrierSupport z₀ (r := a),
          ∀ θ ∈ closedDirections η r,
            NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O) ∧
        ∀ detector : Euclidean (n - 1) → ℂ,
          (∀ ξ, detector ξ ≠ 0 → NormedSpace.normalize ξ ∈ closedDirections η r) →
          ∀ z ∈ parameter '' carrierSupport z₀ (r := a),
            ∀ θ ∈ Sampling.detectorDirectionSupport detector,
              NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O := by
  obtain ⟨d, hd, r, hr, _, hparam, hchart, _⟩ :=
    Sampling.exists_frozenDetector_chart_buffer T hP hz₀ hk hinc hO hkO zero_lt_one
  obtain ⟨aMax, haMax, _, hcarrier⟩ :=
    exists_carrierSupport_in_parameter_ball z₀ hd zero_lt_one
  have hη := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  refine ⟨aMax, angularWidth _ r, haMax, (angularWidth_spec hη hr).1, ?_⟩
  intro a r' η ha hdir hwidth
  have hs : carrierSupport z₀ (r := a) ⊆ carrierSupport z₀ (r := aMax) := by
    intro p hp
    exact ⟨closedBall_subset_closedBall (by linarith) hp.1,
      closedBall_subset_closedBall (by linarith) hp.2⟩
  have hZ : parameter '' carrierSupport z₀ (r := a) ⊆ closedBall z₀ d := by
    rintro _ ⟨p, hp, rfl⟩
    exact ball_subset_closedBall (hcarrier (hs hp))
  have hdirs : closedDirections η r' ⊆
      closedDirections (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) r := by
    intro θ hθ
    refine ⟨hθ.1, ?_⟩
    rw [← hdir]
    exact closedBall_subset_closedBall (by linarith) hθ.2
  have hinside : ∀ z ∈ parameter '' carrierSupport z₀ (r := a),
      ∀ θ ∈ closedDirections η r',
        NormedSpace.normalize (Sampling.frozenInputCovector T z θ) ∈ O :=
    fun z hz θ hθ ↦ hchart r le_rfl z (hZ hz) θ (hdirs hθ)
  refine ⟨(fun p hp ↦ hparam (hZ ⟨p, hp, rfl⟩)), hinside, ?_⟩
  intro detector hdet z hz θ hθ
  exact hinside z hz θ
    (Sampling.detectorDirectionSupport_subset_closedDirections detector η r' hdet hθ)

end JanetCartan.ContinuumRow.NormalizedSelection
