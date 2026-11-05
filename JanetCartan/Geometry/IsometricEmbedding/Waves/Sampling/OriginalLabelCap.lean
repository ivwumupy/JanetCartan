module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicSupport
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier
open CanonicalConic NormalizedSelection SeparatedSampling FullPhaseCharts.ActualComparison

/-- One cap puts every smaller original carrier weight inside the original
parameter cube and the strict graph ball required by the sharp-band estimate.
The cap is chosen before the source scale and all histories; the weight itself
is unchanged (`app:ch_waves:thm:sampling`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_originalConic_sampling_label_cap
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ cap > (0 : ℝ), ∀ b : ℝ, ∀ hb : 0 < b, b ≤ cap → ∀ z : Point,
      originalConicCarrierWeight z₀ hb z ≠ 0 →
        WithLp.toLp 2 z ∈ parameterCube P.radius ∧
        (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
          ball (z₀, T.reference.spatialPatch z₀) (ρ / 4) := by
  obtain ⟨rgraph, hrgraph, hgraph⟩ := exists_originalConic_sampling_support_cap
    T hP hz₀ (half_pos hρ) isOpen_univ (Set.mem_univ _)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_parameterInterior P.radius).mem_nhds hz₀)
  obtain ⟨rparam, hrparam, _hsmall, hparameter⟩ :=
    exists_carrierSupport_in_parameter_ball z₀ hε zero_lt_one
  refine ⟨min rgraph rparam, lt_min hrgraph hrparam, ?_⟩
  intro b hb hbcap z hz
  have hpar := originalConicCarrierWeight_parameter_support z₀ hb hz
  have hgraph' := (hgraph b (hbcap.trans (min_le_left _ _))).1 hpar
  refine ⟨?_, closedBall_subset_ball (by linarith) hgraph'⟩
  obtain ⟨q, hq, heq⟩ := hpar
  have hqp : q ∈ carrierSupport z₀ (r := rparam) :=
    ⟨closedBall_subset_closedBall (by linarith [hbcap.trans (min_le_right _ _)]) hq.1,
      closedBall_subset_closedBall (by linarith [hbcap.trans (min_le_right _ _)]) hq.2⟩
  have hp := hεsub (hparameter hqp)
  rw [heq] at hp
  exact fun i ↦ (hp i).le
end JanetCartan.Sampling
