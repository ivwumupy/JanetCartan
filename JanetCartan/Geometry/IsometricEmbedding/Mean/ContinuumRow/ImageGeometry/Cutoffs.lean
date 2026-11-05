module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization

/-!
# Fixed cutoffs for the geometric image channel

The row producer chooses the physical measurement and source cutoffs before
the current map. This module periodizes each such cutoff inside the coefficient
agreement region of `app:ch_background:defn:bg-row`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumRow.ImageGeometry

open Periodization

variable {n : ℕ}

/-- The physical support fits the centered periodization box
(`app:ch_background:defn:bg-row`). -/
theorem imageCutoff_support_box {ψ : Euclidean n → ℝ} {r : ℝ}
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r) :
    tsupport ψ ⊆ {x | ∀ i, |x i| ≤ r} := by
  intro x hx i
  exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp (hs hx))

/-- The literal periodic measurement or source cutoff used in the image channel
(`app:ch_background:defn:bg-row`). Its physical data are fixed before `F`. -/
def periodizedImageCutoff {r : ℝ} (hr : r < 1 / 2)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r) : C(Torus n, ℝ) :=
  ⟨realPeriodization ψ, (isSmoothPeriodic_realPeriodization hr (imageCutoff_support_box hs) hψ).1⟩

/-- Smoothness of the fixed image cutoff (`app:ch_background:defn:bg-row`). -/
theorem isSmoothPeriodic_periodizedImageCutoff {r : ℝ} (hr : r < 1 / 2)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r) :
    IsSmoothPeriodic (periodizedImageCutoff hr ψ hψ hs) :=
  isSmoothPeriodic_realPeriodization hr (imageCutoff_support_box hs) hψ

/-- The periodic cutoff uses the same centered representative as the coefficient
extension (`app:ch_background:defn:bg-row`). -/
@[simp] theorem periodizedImageCutoff_apply {r : ℝ} (hr : r < 1 / 2)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r) (z : Torus n) :
    periodizedImageCutoff hr ψ hψ hs z = ψ (AmplitudeBound.centeredTorusRepresentative z) := rfl

/-- On the closed fundamental cell the cutoff and all its jets are unchanged
(`app:ch_background:defn:bg-row`). -/
theorem periodizedImageCutoff_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) :
    periodicLift (periodizedImageCutoff hr ψ hψ hs) =ᶠ[𝓝 x] ψ :=
  realPeriodization_eventuallyEq hr (imageCutoff_support_box hs) hx

/-- A cutoff valued in `[0,1]` has torus sup norm at most one
(`app:ch_background:prop:bg-frame`). -/
theorem norm_periodizedImageCutoff_le_one {r : ℝ} (hr : r < 1 / 2)
    (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Metric.closedBall 0 r) (hψrange : ∀ x, ψ x ∈ Icc (0 : ℝ) 1) :
    ‖periodizedImageCutoff hr ψ hψ hs‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro z
  change ‖ψ _‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (hψrange _).1]
  exact (hψrange _).2

end JanetCartan.ContinuumRow.ImageGeometry
