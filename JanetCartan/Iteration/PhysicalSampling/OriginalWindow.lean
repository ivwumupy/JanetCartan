module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Window

/-!
# One concrete window for the common original sampling event

A single normalized real bump gives the mollifier of the manuscript's
convolved box window. It is independent of every original row, source scale,
physical history and sample. This one-dimensional mollifier is NOT the
row-dependent joint amplitude cutoff κ and does not normalize or rescale any
original carrier weight (`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalSampling.OriginalWindow
open LatticeQuadrature SeparatedSampling

/-- The fixed one-dimensional smoothing bump, before all original rows. -/
def bump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- One mollifier shared by the scalar, measured and background events. -/
def mollifier : ℝ → ℝ := bump.normed volume

theorem smooth : ContDiff ℝ ∞ mollifier := bump.contDiff_normed

theorem compact : HasCompactSupport mollifier := bump.hasCompactSupport_normed

theorem integrable : Integrable mollifier := bump.integrable_normed

theorem nonneg (x : ℝ) : 0 ≤ mollifier x := bump.nonneg_normed x

theorem mass : ∫ x, mollifier x = 1 := bump.integral_normed

theorem support : Function.support mollifier ⊆ Icc (-(1 / 4)) (1 / 4) := by
  intro x hx
  have hb : x ∈ ball (0 : ℝ) (1 / 4) := by
    change x ∈ Function.support (bump.normed volume) at hx
    rw [bump.support_normed_eq] at hx
    exact hx
  simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using ball_subset_closedBall hb

/-- The literal convolved box window, with one shared mollifier. -/
def window (p : ℕ) : ℝ → ℝ := convolvedBoxWindow mollifier p

theorem window_smooth (p : ℕ) : ContDiff ℝ ∞ (window p) :=
  contDiff_convolvedBoxWindow compact smooth p

theorem window_continuous (p : ℕ) : Continuous (window p) := (window_smooth p).continuous

theorem window_bounds {p : ℕ} (hp : 0 < p) : WindowBounds p (window p) 1 :=
  Sampling.BackgroundQuadrature.convolvedBoxWindow_bounds integrable mass nonneg support hp

end JanetCartan.PhysicalSampling.OriginalWindow
