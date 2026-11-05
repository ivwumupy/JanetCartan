module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The literal inward radial smoothing formula

Definitions for `app:ch_regular_base:eq:extension-radial-formula` in
`paper-v2.tex`. The kernel is a single normalized nonnegative real bump with
compact support strictly inside the radius-`1/4` ball. The finite coefficients
and the scale-dependent physical cutoff are constructed in separate leaves.
Only the literal formula is fixed here; quantitative estimates are proved in
the corresponding construction modules.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- One fixed normalized kernel for the inward average of
`app:ch_regular_base:eq:extension-radial-formula`. The smaller outer radius
ensures that its closed support is contained in the manuscript's open ball. -/
def kernelBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) where
  rIn := 1 / 16
  rOut := 1 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The real nonnegative mass-one kernel of the ball smoother
(`app:ch_regular_base:lem:ball-extension`). -/
def kernel (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  (kernelBump n).normed volume

/-- Positivity of the actual chosen kernel (`app:ch_regular_base:lem:ball-extension`). -/
theorem kernel_nonneg (x : E) : 0 ≤ kernel n x := (kernelBump n).nonneg_normed x

/-- The actual kernel has mass one (`app:ch_regular_base:lem:ball-extension`). -/
theorem integral_kernel : (∫ y : E, kernel n y) = 1 := (kernelBump n).integral_normed

/-- Global smoothness of the actual fixed kernel
(`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem contDiff_kernel : ContDiff ℝ ∞ (kernel n) := (kernelBump n).contDiff_normed

/-- The actual kernel is integrable (`app:ch_regular_base:lem:ball-extension`). -/
theorem integrable_kernel : Integrable (kernel n) := (kernelBump n).integrable_normed

/-- One fixed compact support for the actual kernel
(`app:ch_regular_base:lem:ball-extension`). -/
theorem hasCompactSupport_kernel : HasCompactSupport (kernel n) :=
  (kernelBump n).hasCompactSupport_normed

/-- The kernel support stays strictly inside the prescribed radius-`1/4`
ball (`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem tsupport_kernel_subset : tsupport (kernel n) ⊆ ball (0 : E) (1 / 4) := by
  rw [kernel, (kernelBump n).tsupport_normed_eq]
  exact closedBall_subset_ball (by norm_num [kernelBump])

/-- The exact inward sampling point, without an extension of the input
(`app:ch_regular_base:eq:extension-radial-formula`). -/
def radialPoint (R : ℝ) (j : ℕ) (x y : E) : E :=
  (1 - (j : ℝ) / R) • x + ((j : ℝ) / R) • y

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal `j`th inward average from the manuscript. Integrability on
the active output collar is proved from the input's closed-ball regularity. -/
def radialAverage (ρ : E → ℝ) (R : ℝ) (j : ℕ) (f : E → F) (x : E) : F :=
  ∫ y, ρ y • f (radialPoint R j x y)

/-- The finite moment combination before physical output multiplication
(`app:ch_regular_base:eq:extension-radial-formula`). The final operator uses
the actual coefficients `coefficient m` from the `Moments` module. -/
def radialCombination (a : ℕ → ℝ) (ρ : E → ℝ) (R : ℝ) (m : ℕ)
    (f : E → F) (x : E) : F :=
  ∑ j ∈ Finset.Icc 1 m, a j • radialAverage ρ R j f x

/-- The literal masked finite radial formula. For the actual physical cutoff
its value is zero outside the expanded collar, exactly as in
`app:ch_regular_base:eq:extension-radial-formula`. -/
def radialSmoothing (χ : E → ℝ) (a : ℕ → ℝ) (ρ : E → ℝ)
    (R : ℝ) (m : ℕ) (f : E → F) (x : E) : F :=
  χ x • radialCombination a ρ R m f x

end JanetCartan.BallSmoothing
