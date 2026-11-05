module

public import JanetCartan.Iteration.PhysicalSeed.OriginalBoundary
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Geometry

/-!
# Fixed geometric inputs of the strengthened original initializer

Use only the ONE actual `PhysicalSeed.OriginalBoundary`. The finite leading
threshold and full-strain threshold are intersected before the arbitrary frame
callback. The original positive extension ball and its collar are constructed
on the same wide chart. These choices neither select another reference nor
change any current carrier, row, or phase.

Consumers: the same-source parameter choice, `exists_history_leading_admission`,
and the literal full-strain source estimate (`new:sec:order-of-choices`,
`main:prop:seed`, `main:prop:current-waves`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open PhysicalSeed ActualCarriers.CurrentFullPhase

variable {n : ℕ}

/-- The patch indices are those of the single strengthened original cover. -/
abbrev OriginalPatchIndex (hn : 5 ≤ n) :=
  (j : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount j)

/-- One positive tolerance meets every actual retained leading tolerance and
its exact order-six conversion factor, the full-strain frame threshold, and
any further positive original-data threshold. All occur BEFORE the arbitrary
reference-frame callback (`new:sec:order-of-choices`). -/
theorem exists_original_common_frame_tolerance (hn : 5 ≤ n)
    {extra : ℝ} (hextra : 0 < extra) :
    ∃ εframe : ℝ, 0 < εframe ∧ εframe ≤ extra ∧
      εframe ≤ RawPrimary.ambientStrainFrameThreshold hn / 2 ∧
      ∀ i : OriginalPatchIndex hn,
        εframe ≤ (OriginalBoundary.η hn i / (2 * (6 + 1 : ℝ))) / 2 := by
  classical
  let base := min extra (RawPrimary.ambientStrainFrameThreshold hn / 2)
  have hbase : 0 < base := lt_min hextra
    (half_pos (RawPrimary.ambientStrainFrameThreshold_pos hn))
  let bounds : Finset ℝ := insert base (Finset.univ.image
    (fun i : OriginalPatchIndex hn ↦
      (OriginalBoundary.η hn i / (2 * (6 + 1 : ℝ))) / 2))
  have hnonempty : bounds.Nonempty := Finset.insert_nonempty _ _
  let εframe := bounds.min' hnonempty
  have hpositive : 0 < εframe := by
    have hp : ∀ t ∈ bounds, 0 < t := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hbase
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
        exact half_pos (div_pos (OriginalBoundary.η_pos hn i) (by norm_num))
    exact hp _ (bounds.min'_mem hnonempty)
  have hle : εframe ≤ base := bounds.min'_le base (Finset.mem_insert_self _ _)
  refine ⟨εframe, hpositive, hle.trans (min_le_left _ _),
    hle.trans (min_le_right _ _), ?_⟩
  intro i
  exact bounds.min'_le _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- The extension parameters are constructed on the original wide chart.
The positive collar remains inside that SAME chart and can be used as both
prescribed quotient and full-coefficient extension (`main:prop:seed`). -/
def originalBallExtension (hn : 5 ≤ n) : BallExtension.Parameters (Euclidean n) :=
  Classical.choose (BallExtension.exists_parameters (0 : Euclidean n)
    (OriginalBoundary.b_pos hn) isOpen_ball
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)))

/-- The fixed extension is centered at the original base point. -/
theorem originalBallExtension_center (hn : 5 ≤ n) :
    (originalBallExtension hn).center = 0 :=
  (Classical.choose_spec (BallExtension.exists_parameters (0 : Euclidean n)
    (OriginalBoundary.b_pos hn) isOpen_ball
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)))).1

/-- Its radius is literally the original coefficient radius. -/
theorem originalBallExtension_radius (hn : 5 ≤ n) :
    (originalBallExtension hn).radius = OriginalBoundary.b hn :=
  (Classical.choose_spec (BallExtension.exists_parameters (0 : Euclidean n)
    (OriginalBoundary.b_pos hn) isOpen_ball
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)))).2.1

/-- The extension collar stays on the original physical construction chart. -/
theorem originalBallExtension_collar (hn : 5 ≤ n) :
    closedBall (originalBallExtension hn).center
        ((originalBallExtension hn).radius + (originalBallExtension hn).width) ⊆
      ball (0 : Euclidean n) (OriginalBoundary.R hn) :=
  (Classical.choose_spec (BallExtension.exists_parameters (0 : Euclidean n)
    (OriginalBoundary.b_pos hn) isOpen_ball
    (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)))).2.2

/-- The coefficient frame balls of the actual retained Hamilton families lie
in the SAME original coefficient ball; no enlargement of their inner-state
certificates is performed (`app:ch_seed:prop:seed-actual-menu`). -/
theorem original_frameBall_subset (hn : 5 ≤ n) (i : OriginalPatchIndex hn) :
    closedBall (0 : Euclidean n)
      (OriginalBoundary.T hn i).data.localReference.stateRadius ⊆
        closedBall 0 (OriginalBoundary.b hn) := by
  exact (frameBall_subset_of_stateDomain
    (OriginalBoundary.T hn i).data.localReference
    (OriginalBoundary.stateDomain_subset_ball hn i)).trans ball_subset_closedBall

/-- The original common radius already has a factor-three buffer inside
EVERY original physical phase domain (`main:prop:patches`). -/
theorem original_phase_radius_buffer (hn : 5 ≤ n) (i : OriginalPatchIndex hn) :
    3 * OriginalBoundary.r hn < (OriginalBoundary.T hn i).physicalRadius := by
  exact OriginalBoundary.three_mul_r_lt_referenceRadius hn i

/-- A fixed compact phase core fits every retained original physical domain.
This core is chosen before regular masks, samples, and final source dilation. -/
theorem original_phase_core_subset (hn : 5 ≤ n) (i : OriginalPatchIndex hn) :
    closedBall (0 : Euclidean n) (OriginalBoundary.r hn) ⊆
      ball 0 (OriginalBoundary.T hn i).physicalRadius := by
  apply closedBall_subset_ball
  have hp := OriginalBoundary.r_pos hn
  have hb := original_phase_radius_buffer hn i
  linarith

/-- The retained incidence centers are nonzero, as required by the original
arbitrary-quotient callback. No new center is chosen (`main:prop:seed`). -/
theorem original_kCenter_ne_zero (hn : 5 ≤ n) (i : OriginalPatchIndex hn) :
    OriginalBoundary.kCenter hn i.1 ≠ 0 := by
  intro hz
  have hs := OriginalBoundary.kCenter_mem_sphere hn i.1
  rw [hz] at hs
  simp at hs

end JanetCartan.PhysicalInitialization
