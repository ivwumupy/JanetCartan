module

public import JanetCartan.Iteration.RevisedUniform.OriginalCore
public import JanetCartan.Geometry.IsometricEmbedding.Response.SourceExtension.Cutoff
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasksTemplate

/-!
# Literal original full-source masks and product geometry

The envelope cutoff is the already chosen χ₃, with the actual fixed defect
core D and the original inverse chart. Neither its function nor the broader
measured χsrc is recut. Every parameter window is the original open doubled
cell, retaining independent label and covector variation. All objects precede
the source contraction, histories and samples (`app:ch_response:eq:response-graded-source`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalSourceMasks
open PhysicalInitialization PhysicalSeed ResponseSourceExtension
open RegularSector.FiniteMasks.ActualFamily

/-- Package the same bump as an output cutoff. Its function is not selected
again, and its plateau uses the actual fixed-core neighborhood certificate. -/
def bumpOutputCutoff {n : ℕ} (core chart : Set (Euclidean n))
    (χ : ContDiffBump (0 : Euclidean n))
    (hsupport : tsupport (χ : Euclidean n → ℝ) ⊆ chart)
    (hplateau : ∀ y ∈ core, (χ : Euclidean n → ℝ) =ᶠ[𝓝 y] (fun _ ↦ 1)) :
    OutputCutoff core chart where
  toFun := χ
  smooth := χ.contDiff
  compact := χ.hasCompactSupport
  support_chart := hsupport
  plateau := fun y hy ↦ mem_interior_iff_mem_nhds.mpr (hplateau y hy)

theorem bumpOutputCutoff_toFun {n : ℕ} (core chart : Set (Euclidean n))
    (χ : ContDiffBump (0 : Euclidean n))
    (hsupport : tsupport (χ : Euclidean n → ℝ) ⊆ chart)
    (hplateau : ∀ y ∈ core, (χ : Euclidean n → ℝ) =ᶠ[𝓝 y] (fun _ ↦ 1)) :
    (bumpOutputCutoff core chart χ hsupport hplateau).toFun = (χ : Euclidean n → ℝ) := rfl

theorem bump_properties {n : ℕ} (χ : ContDiffBump (0 : Euclidean n)) :
    ContDiff ℝ ∞ (χ : Euclidean n → ℝ) ∧ HasCompactSupport (χ : Euclidean n → ℝ) :=
  ⟨χ.contDiff, χ.hasCompactSupport⟩

theorem original_chart_open (n : ℕ) (radius : ℝ) :
    IsOpen (ball (0 : Euclidean n) radius) := isOpen_ball

theorem measured_source_smooth {n : ℕ} {μ : ℝ} (hμ : 0 < μ) :
    ContDiff ℝ ∞ (OriginalRegular.measuredSourceCutoff (n := n) hμ) :=
  (ContinuumRow.FixedCutoffs.physical hμ (2 : Fin 3)).contDiff

/-- Exactly the original open doubled parameter cell, not a new parameter
cutoff or a frozen reference-covector graph. -/
def parameterWindow {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (j : OriginalBoundary.centers hn a) : Set (Euclidean 3 × Euclidean (n-1)) :=
  ball (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
    (2 * OriginalBoundary.σcover hn a j)

theorem parameterWindow_spec {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (j : OriginalBoundary.centers hn a) :
    IsOpen (parameterWindow hn a j) ∧
    parameterWindow hn a j ⊆ OriginalRegular.wholeWindow hn a ∧
    IsCompact (closure (parameterWindow hn a j)) ∧
    closure (parameterWindow hn a j) ⊆ OriginalProtected.Csrc hn a ∧
    closedBall (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
      (OriginalBoundary.σcover hn a j) ⊆ parameterWindow hn a j := by
  have hσ := (OriginalBoundary.comparison_pos hn a j).2.2.2.2.2.2.2.2
  have hsub : parameterWindow hn a j ⊆ OriginalRegular.wholeWindow hn a :=
    subset_iUnion (fun k : OriginalBoundary.centers hn a ↦ parameterWindow hn a k) j
  refine ⟨isOpen_ball, hsub, ?_, ?_, ?_⟩
  · exact (OriginalRegular.wholeWindow_spec hn a).2.1.of_isClosed_subset isClosed_closure (closure_mono hsub)
  · exact (closure_mono hsub).trans (OriginalRegular.wholeWindow_spec hn a).2.2.1
  · exact closedBall_subset_ball (by linarith : OriginalBoundary.σcover hn a j < 2 * OriginalBoundary.σcover hn a j)

/-- The complete native inverse chart fits every original spatial cell.
Thus its product with the entire doubled parameter window stays in the
same original doubled product ball used by the full-strain envelope. -/
theorem chart_geometry {d : ℕ} (hn : 5 ≤ d+1) (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    {K : Set (Euclidean (d+1))} {M : ℝ}
    (f : ActualMaskFamily (ball 0 (OriginalBoundary.b hn)) 0
      (OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ))
      (cubeStress (d+1)) K M) (t : ℝ) :
    ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ ball 0 (OriginalBoundary.b hn) ∧
    ∀ (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a),
      ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ ball 0 (OriginalBoundary.σcover hn a j) ∧
      ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ×ˢ parameterWindow hn a j ⊆
        closedBall ((0 : Euclidean (d+1)),
          (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val))
          (2 * OriginalBoundary.σcover hn a j) := by
  have hρ := f.physicalRadius_pos
  have hx : ball (0 : Euclidean (d+1)) (min t f.physicalRadius) ⊆ closedBall 0 f.physicalRadius :=
    (ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall
  have hcore := hx.trans ((closedBall_subset_closedBall
    (by linarith only [hρ] : f.physicalRadius ≤ 4*f.physicalRadius)).trans f.physicalBall_coefficientDomain)
  refine ⟨hcore.trans (OriginalRegular.core_spec hn (OriginalRegular.screened_pos hn hr hμ)).2.2.1, ?_⟩
  intro a j
  have hs := (OriginalRegular.core_inside_native_cutoffs hn hr hμ).2.2 a j
  have hcell := hcore.trans (closedBall_subset_ball hs)
  have hσ := (OriginalBoundary.comparison_pos hn a j).2.2.2.2.2.2.2.2
  refine ⟨hcell, ?_⟩
  intro w hw
  rw [← closedBall_prod_same]
  exact ⟨ball_subset_closedBall ((ball_subset_ball (by linarith :
    OriginalBoundary.σcover hn a j ≤ 2 * OriginalBoundary.σcover hn a j)) (hcell hw.1)),
    ball_subset_closedBall hw.2⟩

theorem output_support_in_coefficient_ball {n : ℕ} {core chart : Set (Euclidean n)}
    (χenv : OutputCutoff core chart) (b : ℝ) (hchart : chart ⊆ ball (0 : Euclidean n) b) :
    tsupport χenv.toFun ⊆ closedBall (0 : Euclidean n) b :=
  χenv.support_chart.trans (hchart.trans ball_subset_closedBall)

end JanetCartan.PhysicalPrimary.OriginalSourceMasks

retain_actual_original_source_masks
