module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public meta import JanetCartan.Iteration.RevisedUniform.OriginalCoreTemplate

/-!
# The fixed core of the actual original physical correction

The defect core is **defined** from the same original23 inverse bump χ₂:
`D = closedBall 0 (χ₂.rIn / 2)`. No source contraction, finite history, target,
accuracy, successful PDE estimate or new mask is supplied to choose it.

The construction provides the fixed compact core of `main:thm:step`, strictly
inside the actual normalized inverse PDE domain (`app:ch_regular:eq:exact-physical`).
The original χ₃ envelope cutoff, real measured source cutoff and inverse input
mask retain their own plateaus on this core. The full original independent
label/covector source domains are unchanged. This does not assert an analytic
correction estimate or the unconditional Main.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter
open scoped Topology
namespace JanetCartan.RevisedUniform.OriginalCore
open PhysicalInitialization PhysicalSeed

/-- A fixed half-radius core lies strictly inside the selected inverse bump's
PDE plateau, with the origin in its interior (`main:thm:step`). -/
theorem inverse_bump_core_spec {n : ℕ} (χ : ContDiffBump (0 : Euclidean n)) :
    0 < χ.rIn / 2 ∧
    IsCompact (closedBall (0 : Euclidean n) (χ.rIn / 2)) ∧
    (closedBall (0 : Euclidean n) (χ.rIn / 2)).Nonempty ∧
    (0 : Euclidean n) ∈ interior (closedBall (0 : Euclidean n) (χ.rIn / 2)) ∧
    (interior (closedBall (0 : Euclidean n) (χ.rIn / 2))).Nonempty ∧
    closedBall (0 : Euclidean n) (χ.rIn / 2) ⊆ ball 0 χ.rIn ∧
    (∀ y ∈ closedBall (0 : Euclidean n) (χ.rIn / 2), χ y = 1) ∧
    closedBall (0 : Euclidean n) (χ.rIn / 2) ⊆ tsupport (χ : Euclidean n → ℝ) := by
  have hhalf : 0 < χ.rIn / 2 := half_pos χ.rIn_pos
  have hlt : χ.rIn / 2 < χ.rIn := half_lt_self χ.rIn_pos
  have hsub : closedBall (0 : Euclidean n) (χ.rIn / 2) ⊆ ball 0 χ.rIn :=
    closedBall_subset_ball hlt
  have hplateau : ∀ y ∈ closedBall (0 : Euclidean n) (χ.rIn / 2), χ y = 1 :=
    fun y hy ↦ χ.one_of_mem_closedBall (ball_subset_closedBall (hsub hy))
  have hint : (0 : Euclidean n) ∈ interior (closedBall (0 : Euclidean n) (χ.rIn / 2)) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds (0 : Euclidean n) hhalf) ball_subset_closedBall)
  refine ⟨hhalf, isCompact_closedBall _ _, ⟨0, mem_closedBall_self hhalf.le⟩,
    hint, ⟨0, hint⟩, hsub, hplateau, ?_⟩
  intro y hy
  apply subset_tsupport (χ : Euclidean n → ℝ)
  change χ y ≠ 0
  rw [hplateau y hy]
  exact one_ne_zero

/-- Use the existing native nested cutoff and measured/input plateaus; no
replacement envelope or source mask is selected on the smaller defect core. -/
theorem inverse_bump_core_masks {n : ℕ} (χ₂ χ₃ : ContDiffBump (0 : Euclidean n))
    (χsrc input : Euclidean n → ℝ)
    (hnest : ∀ y ∈ tsupport (χ₂ : Euclidean n → ℝ), χ₃ y = 1)
    (hsrc : ∀ y ∈ tsupport (χ₂ : Euclidean n → ℝ), χsrc =ᶠ[𝓝 y] (fun _ ↦ 1))
    (hinput : ∀ y ∈ tsupport (χ₂ : Euclidean n → ℝ), input =ᶠ[𝓝 y] (fun _ ↦ 1)) :
    ∀ y ∈ closedBall (0 : Euclidean n) (χ₂.rIn / 2),
      (χ₂ : Euclidean n → ℝ) =ᶠ[𝓝 y] (fun _ ↦ 1) ∧
      (χ₃ : Euclidean n → ℝ) =ᶠ[𝓝 y] (fun _ ↦ 1) ∧
      χsrc =ᶠ[𝓝 y] (fun _ ↦ 1) ∧ input =ᶠ[𝓝 y] (fun _ ↦ 1) := by
  intro y hy
  have hyb : y ∈ ball (0 : Euclidean n) χ₂.rIn :=
    closedBall_subset_ball (half_lt_self χ₂.rIn_pos) hy
  have hone z (hz : z ∈ ball (0 : Euclidean n) χ₂.rIn) : χ₂ z = 1 :=
    χ₂.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hs z (hz : z ∈ ball (0 : Euclidean n) χ₂.rIn) :
      z ∈ tsupport (χ₂ : Euclidean n → ℝ) := by
    apply subset_tsupport (χ₂ : Euclidean n → ℝ)
    change χ₂ z ≠ 0
    rw [hone z hz]
    exact one_ne_zero
  refine ⟨?_, ?_, hsrc y (hs y hyb), hinput y (hs y hyb)⟩
  · filter_upwards [isOpen_ball.mem_nhds hyb] with z hz
    exact hone z hz
  · filter_upwards [isOpen_ball.mem_nhds hyb] with z hz
    exact hnest z (hs z hz)

/-- Actual original full-source cells, physical domains and coefficient chart
contain the same fixed defect core. The source product's native support bound
is used in its proved direction, not as a small-support assumption on χsrc. -/
theorem inverse_bump_core_source_geometry {n : ℕ} (hn : 5 ≤ n)
    (χ₂ : ContDiffBump (0 : Euclidean n)) (χsrc : Euclidean n → ℝ)
    (hmul : (fun y ↦ χsrc y * χ₂ y) = (χ₂ : Euclidean n → ℝ))
    (hcell : ∀ (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a),
      tsupport (fun y ↦ χsrc y * χ₂ y) ⊆
        OriginalProtected.Xsrc hn a ∩ ball 0 (OriginalBoundary.σcover hn a j)) :
    ∀ a : OriginalPatchIndex hn,
      (∀ j : OriginalBoundary.centers hn a,
        closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆
          OriginalProtected.Xsrc hn a ∩ ball 0 (OriginalBoundary.σcover hn a j)) ∧
      closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆ OriginalProtected.Xsrc hn a ∧
      closedBall (0 : Euclidean n) (χ₂.rIn / 2) ×ˢ OriginalProtected.Csrc hn a ⊆
        LeadingWave.FullModulation.domain (OriginalBoundary.T hn a) ∧
      closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆ ball 0 (OriginalBoundary.T hn a).physicalRadius ∧
      closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆ ball 0 (OriginalBoundary.b hn) := by
  intro a
  have hs : closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆
      tsupport (fun y ↦ χsrc y * χ₂ y) := by
    rw [hmul]
    exact (inverse_bump_core_spec χ₂).2.2.2.2.2.2.2
  have hall (j : OriginalBoundary.centers hn a) := hs.trans (hcell a j)
  obtain ⟨q, hq⟩ := OriginalRegular.original_source_nonempty hn a
  obtain ⟨j, _⟩ := Set.mem_iUnion.mp hq.2
  have hX : closedBall (0 : Euclidean n) (χ₂.rIn / 2) ⊆ OriginalProtected.Xsrc hn a :=
    fun _ hy ↦ (hall j hy).1
  exact ⟨hall, hX,
    (Set.prod_mono hX (Subset.refl _)).trans (OriginalProtected.source_domains hn a).2.2.2.1,
    hX.trans (OriginalProtected.source_domains hn a).2.2.2.2,
    hX.trans (closedBall_subset_ball (OriginalProtected.sourceRadius_lt_b hn))⟩

end JanetCartan.RevisedUniform.OriginalCore

retain_actual_original_defect_core
