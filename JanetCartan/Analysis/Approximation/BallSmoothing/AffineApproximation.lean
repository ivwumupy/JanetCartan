module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Affine
public import JanetCartan.Analysis.Approximation.BallSmoothing.Approximation

/-!
# Approximation on the original ball

This transports the proved finite-moment Taylor estimate to the original
closed ball. The SAME smoother uses exactly `m` original input derivatives;
only a fixed radius-dependent factor enters the constant in
`app:ch_regular_base:eq:ball-extension-continuous`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Exact `R⁻ᵐ` approximation by the actual real smoother on the original
closed ball. The input norm uses exactly the original `m` derivatives
(`app:ch_regular_base:eq:ball-extension-continuous`). -/
theorem cNorm_affineSmoothing_sub_le (c : E) {a : ℝ} (ha : 0 < a)
    {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    (f : E → F) (hf : ∀ x ∈ closedBall c a, ContDiffAt ℝ ∞ f x) :
    cNorm (closedBall c a) 0 (f - affineSmoothing c a R m f) ≤
      (radialApproximationConstant m * (∑ j ∈ Finset.range (m + 1), a ^ j)) *
        (R⁻¹)^m * cNorm (closedBall c a) m f := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : 0 ≤ R := by linarith
  have hA : 0 ≤ ∑ j ∈ Finset.range (m + 1), a ^ j :=
    Finset.sum_nonneg fun j _ ↦ pow_nonneg ha.le _
  rw [cNorm_order_zero]
  apply Real.sSup_le
  · rintro _ ⟨x, hx, rfl⟩
    have hb := norm_radialSmoothing_sub_le hm hR (fun z ↦ f (ballRescale c a z))
      (contDiffAt_ballRescale_closedBall c ha.le hf) (ballNormalize_mem_closedBall c ha hx)
    change ‖affineSmoothing c a R m f x - f (ballRescale c a (ballNormalize c a x))‖ ≤ _ at hb
    rw [ballRescale_ballNormalize c ha.ne' x] at hb
    have hnorm := cNorm_ballRescale_le c ha m
      (fun x hx ↦ (hf x hx).of_le (by simp))
    calc
      ‖(f - affineSmoothing c a R m f) x‖ = ‖affineSmoothing c a R m f x - f x‖ :=
        norm_sub_rev _ _
      _ ≤ radialApproximationConstant m * (R⁻¹)^m *
          cNorm (closedBall (0 : E) 1) m (fun z ↦ f (ballRescale c a z)) := hb
      _ ≤ radialApproximationConstant m * (R⁻¹)^m *
          ((∑ j ∈ Finset.range (m + 1), a ^ j) * cNorm (closedBall c a) m f) :=
        mul_le_mul_of_nonneg_left hnorm
          (mul_nonneg (radialApproximationConstant_nonneg _) (pow_nonneg (inv_nonneg.mpr hR0) _))
      _ = _ := by ring
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (radialApproximationConstant_nonneg _) hA)
      (pow_nonneg (inv_nonneg.mpr hR0) _)) (cNorm_nonneg _ _ _)

end JanetCartan.BallSmoothing
