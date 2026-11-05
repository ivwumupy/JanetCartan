module

public import JanetCartan.Iteration.PhysicalSeed.RootBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CompatibleWorkingBalls

/-!
# One actual original sampling radius, before source scale or budgets

The radius is chosen on the original incidence, patch and retained parent. Its
whole carrier projection stays in that parent's original compatible cell, its
full phase ball stays in the original static leading window, and its parameter
support stays in the original cube. The same positive radius is used by the
scalar, measured corrected and finite-normal comparison factories. Irrelevant
parent indices get the positive value one; the actual selected parent satisfies
the good branch by `PhysicalSeed.selected_root_static_buffers`/`fact1`.

No source, parent, flow or original conic selector is chosen here. The consumer
is the original common scalar/corrected event, `new:sec:order-of-choices` and
`app:ch_waves:thm:sampling`.
-/

@[expose] public noncomputable section
open Set Metric

namespace JanetCartan.PhysicalSampling
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalConic
open CanonicalCarrier LeadingPrimitive Sampling PhysicalSeed FullPhaseCharts.ActualComparison
open LeadingWave.FullModulation

/-- Construct the actual shared working ball in the SAME original compatible
cell. This is before the reference, source scale, or analytic budgets. -/
theorem exists_original_sampling_workingRadius {n : ℕ} (hn : 5 ≤ n)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let zRoot := (OriginalBoundary.D hn).roots q.1.1 l q.1.2
    let graphRoot := ((0 : Euclidean n), (zRoot, T.reference.spatialPatch zRoot))
    let cell := ball (0 : Euclidean n) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) ×ˢ
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)
    ∃ ρ > (0 : ℝ),
      closedBall graphRoot (2 * ρ) ⊆
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1))
          (OriginalBoundary.σcover hn ⟨q.1.1, l⟩ j) ∧
      closedBall graphRoot (2 * ρ) ⊆ domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ) ⊆
        closedBall 0 T.data.localReference.stateRadius ∧
      closedBall zRoot (2 * ρ) ⊆ parameterInterior
        (2 * ((OriginalBoundary.D hn).patches q.1.1 l).radius) ∧
      closedBall zRoot (ρ / 4) ⊆ parameterCube
        ((OriginalBoundary.D hn).patches q.1.1 l).radius ∧
      MapsTo (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        (w.1, (w.2.1 0, spectatorCenter w.2.1)))
        (closedBall graphRoot (2 * ρ)) cell := by
  intro T zRoot graphRoot cell
  have hP := ((OriginalBoundary.hD hn).2.2.2.2.1 q.1.1 l).1
  have hzRoot := (original_root_static_buffers hn q l j hroot).2.2.2
  have hcell := OriginalBoundary.carrier_cells hn ⟨q.1.1, l⟩ j
  have hpoint : ((0 : Euclidean n), (zRoot 0, spectatorCenter zRoot)) ∈ cell :=
    ⟨mem_ball_self hcell.1, hroot⟩
  obtain ⟨ρ₀, hρ₀, hparent, hphase, hspace, hcarrier, hproject⟩ :=
    exists_sampling_workingBall_in_compatible_cell hP T
      (K := closedBall 0 T.data.localReference.stateRadius) (Subset.refl _)
      (fun i ↦ (hzRoot i).le) (isOpen_ball.prod isOpen_ball) hpoint hcell.2.2.1
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_parameterInterior _).mem_nhds hzRoot)
  let ρ := min ρ₀ s
  have hρ : 0 < ρ := lt_min hρ₀ hs
  have hle : 2 * ρ ≤ 2 * ρ₀ :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  refine ⟨ρ, hρ, (closedBall_subset_closedBall hle).trans hparent,
    (closedBall_subset_closedBall hle).trans hphase,
    (closedBall_subset_closedBall hle).trans hspace,
    (closedBall_subset_closedBall hle).trans hcarrier, ?_, ?_⟩
  · intro z hz i
    have hz' : z ∈ closedBall zRoot s := closedBall_subset_closedBall
      (by have hρs : ρ ≤ s := min_le_right _ _; linarith : ρ / 4 ≤ s) hz
    exact (hsub hz' i).le
  · exact hproject.mono_left (closedBall_subset_closedBall hle)

/-- The one shared actual radius on every original preselection slot. The
irrelevant-parent branch is only to define the original all-cells callback. -/
def originalSamplingRadius {n : ℕ} (hn : 5 ≤ n)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩) : {ρ : ℝ // 0 < ρ} := by
  classical
  exact if hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
      spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
    ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) then
    ⟨(exists_original_sampling_workingRadius hn q l j hroot).choose,
      (exists_original_sampling_workingRadius hn q l j hroot).choose_spec.1⟩
  else ⟨1, zero_lt_one⟩

/-- The literal named shared radius has every original support certificate on
an admitted parent. The actual selected row supplies `hroot` by `fact1`; the
radius must not be chosen again by any analytic factory. -/
theorem originalSamplingRadius_spec {n : ℕ} (hn : 5 ≤ n)
    (q : IncidenceCenter (OriginalBoundary.D hn))
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1))
    (j : OriginalBoundary.centers hn ⟨q.1.1, l⟩)
    (hroot : ((OriginalBoundary.D hn).roots q.1.1 l q.1.2 0,
        spectatorCenter ((OriginalBoundary.D hn).roots q.1.1 l q.1.2)) ∈
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)) :
    let ρ : ℝ := originalSamplingRadius hn q l j
    let T := OriginalBoundary.T hn ⟨q.1.1, l⟩
    let zRoot := (OriginalBoundary.D hn).roots q.1.1 l q.1.2
    let graphRoot := ((0 : Euclidean n), (zRoot, T.reference.spatialPatch zRoot))
    let cell := ball (0 : Euclidean n) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j) ×ˢ
      ball (j.1.1 0, spectatorCenter j.1.1) (OriginalBoundary.εcarrier hn ⟨q.1.1, l⟩ j)
    closedBall graphRoot (2 * ρ) ⊆
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1))
          (OriginalBoundary.σcover hn ⟨q.1.1, l⟩ j) ∧
      closedBall graphRoot (2 * ρ) ⊆ domain T ∧
      closedBall (0 : Euclidean n) (2 * ρ) ⊆
        closedBall 0 T.data.localReference.stateRadius ∧
      closedBall zRoot (2 * ρ) ⊆ parameterInterior
        (2 * ((OriginalBoundary.D hn).patches q.1.1 l).radius) ∧
      closedBall zRoot (ρ / 4) ⊆ parameterCube
        ((OriginalBoundary.D hn).patches q.1.1 l).radius ∧
      MapsTo (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        (w.1, (w.2.1 0, spectatorCenter w.2.1)))
        (closedBall graphRoot (2 * ρ)) cell := by
  simpa only [originalSamplingRadius, dite_eq_left hroot] using
    (exists_original_sampling_workingRadius hn q l j hroot).choose_spec.2

end JanetCartan.PhysicalSampling
