module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# All derivatives fall on the smoothing kernel

The derivative step in `app:ch_regular_base:lem:ball-extension` uses only
the source's uniform norm. The convolution estimate below transfers every
Fréchet derivative to the compactly supported smooth kernel. The bilinear
target is allowed to vary because differentiation produces continuous linear
maps; the actual ball smoother uses real scalar multiplication.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

variable {A B C : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Every derivative of convolution is bounded by the `L¹` norm of the
same-order kernel derivative and the source's `C⁰` bound. This is the
primitive input to `app:ch_regular_base:eq:ball-extension-sobolev`; no
positive-order source derivative is used. -/
theorem norm_iteratedFDeriv_convolution_le_kernel (r : ℕ)
    (L : A →L[ℝ] B →L[ℝ] C) {ψ : E → A} (hc : HasCompactSupport ψ)
    (hψ : ContDiff ℝ ∞ ψ) {f : E → B} (hf : LocallyIntegrable f)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖f x‖ ≤ M) (x : E) :
    ‖iteratedFDeriv ℝ r (ψ ⋆[L] f) x‖ ≤
      ‖L‖ * (∫ y, ‖iteratedFDeriv ℝ r ψ y‖) * M := by
  induction r generalizing A C with
  | zero =>
    simp only [norm_iteratedFDeriv_zero]
    have hi := hc.convolutionExists_left L hψ.continuous hf x
    have hκ : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hc
    calc
      _ ≤ ∫ y, ‖L (ψ y) (f (x - y))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖L‖ * ‖ψ y‖ * M := by
        apply integral_mono hi.norm ((hκ.norm.const_mul ‖L‖).mul_const M)
        intro y
        exact (L.le_opNorm₂ (ψ y) (f (x - y))).trans
          (mul_le_mul_of_nonneg_left (hbound _) (by positivity))
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  | succ r ih =>
    have hD : fderiv ℝ (ψ ⋆[L] f) = (fderiv ℝ ψ ⋆[L.precompL E] f) := by
      funext z
      exact (hc.hasFDerivAt_convolution_left L (hψ.of_le (by simp)) hf z).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hD]
    have h := ih (L.precompL E) (hc.fderiv ℝ) (hψ.fderiv_right (by simp))
    simp only [norm_iteratedFDeriv_fderiv] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (L.norm_precompL_le E)
        (integral_nonneg fun y ↦ norm_nonneg _)) hM)

end JanetCartan.BallSmoothing
