module

public import JanetCartan.Iteration.PhysicalNormalInverse.RetainedProfiles

/-!
# Restrict the retained coefficient profiles to the one sampling ball

The actual working-radius certificate places its doubled ball inside the OPEN
original σcover window. This restriction changes neither the coefficient nor
its profile budget. Consumer: the actual fixed-radius corrected normal
comparison (`app:ch_waves:eq:colored-normal-comparison`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalNormalInverse

/-- The doubled original-root working ball lies in the old inner window. -/
theorem working_ball_subset_retained_ball {n : ℕ}
    {a b : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    {σ ρ : ℝ} (hρ : 0 < ρ)
    (hcontain : closedBall b (2 * ρ) ⊆ ball a σ) :
    closedBall b ρ ⊆ closedBall a σ := by
  exact (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans
    (hcontain.trans ball_subset_closedBall)

/-- Keep the SAME profile constants when moving from the selected-cell window
to its already-chosen original-root working ball. -/
theorem retained_profile_on_working_ball {n : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {a b : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (hcontain : closedBall b (2 * ρ) ⊆ ball a σ)
    {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Z}
    (hf : ContDiffOn ℝ ∞ f (ball a (2 * σ)))
    {r : ℕ} {L : ℝ} {C : ℕ → ℝ}
    (hp : HasDerivativeProfile (closedBall a σ) f r L C) :
    ContDiffOn ℝ ∞ f (ball b (2 * ρ)) ∧
      HasDerivativeProfile (closedBall b ρ) f r L C := by
  have hlarge : ball b (2 * ρ) ⊆ ball a (2 * σ) :=
    (ball_subset_closedBall.trans hcontain).trans
      (ball_subset_ball (by linarith : σ ≤ 2 * σ))
  have hsmall := working_ball_subset_retained_ball hρ hcontain
  have hinner : closedBall a σ ⊆ ball a (2 * σ) :=
    closedBall_subset_ball (by linarith : σ < 2 * σ)
  refine ⟨hf.mono hlarge, ?_⟩
  intro j
  apply (cNorm_mono_set_of_contDiffAt (r := j) (f := f) hsmall
    (isCompact_closedBall _ _)
    (fun w hw ↦ (hf.contDiffAt (isOpen_ball.mem_nhds (hinner hw))).of_le (by simp))).trans
  exact hp j

end JanetCartan.PhysicalNormalInverse
