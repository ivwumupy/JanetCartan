module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Smooth representatives near a closed ball

The localization step for `app:lem:elementary-interpolation-jets` and
`app:ch_seed:eq:seed-frame-tame`: a cutoff turns a function smooth on an open
neighborhood of a closed ball into a globally smooth function with the same
germ at every point of the ball. No bounds outside that ball are needed.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Metric

namespace JanetCartan.ProjectedStressFrame

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:lem:elementary-interpolation-jets`: a map smooth on an arbitrary open
neighborhood of a positive-radius closed ball has a compactly supported global
representative agreeing near each point of the ball. This also preserves every
ambient derivative at boundary points, as needed in `app:ch_seed:eq:seed-frame-tame`.
The codomain need not be complete or finite-dimensional. -/
theorem exists_contDiff_extension_eq_near_closedBall [FiniteDimensional ℝ E]
    (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    {s : Set E} (hs : IsOpen s) (hKs : closedBall x ρ ⊆ s)
    {f : E → F} {n : ℕ∞} (hf : ContDiffOn ℝ n f s) :
    ∃ u : E → F, ContDiff ℝ n u ∧ HasCompactSupport u ∧
      tsupport u ⊆ s ∧ ∀ y ∈ closedBall x ρ, u =ᶠ[𝓝 y] f := by
  obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall x ρ).exists_cthickening_subset_open hs hKs
  rw [cthickening_closedBall hδ.le hρ.le] at hδs
  let φ : ContDiffBump x := ⟨ρ + δ / 2, ρ + δ, by positivity, by linarith⟩
  have hφ : tsupport φ ⊆ s := by
    rw [φ.tsupport_eq]
    simpa only [φ, add_comm] using hδs
  refine ⟨fun y ↦ φ y • f y, ?_, φ.hasCompactSupport.smul_right, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport φ
    · exact φ.contDiffAt.smul (hf.contDiffAt (hs.mem_nhds (hφ hy)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [hz]
  · exact (tsupport_smul_subset_left φ f).trans hφ
  · intro y hy
    have hyφ : y ∈ ball x φ.rIn := (closedBall_subset_ball (by dsimp [φ]; linarith)) hy
    filter_upwards [φ.eventuallyEq_one_of_mem_ball hyφ] with z hz
    simp [hz]

end JanetCartan.ProjectedStressFrame
