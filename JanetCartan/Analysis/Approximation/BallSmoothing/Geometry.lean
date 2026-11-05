module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Basic

/-!
# The inward samples remain in the original ball

The geometric calculation in the proof of
`app:ch_regular_base:eq:extension-radial-formula`. A reflected input scaling
also writes the literal average as a convolution with the one fixed kernel;
this is used to transfer all derivatives to that kernel.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Every active sample in the larger output collar lies strictly in the
original unit ball, including when the output point is on the collar boundary
(`app:ch_regular_base:lem:ball-extension`). -/
theorem radialPoint_mem_ball {R : ℝ} (hR : 0 < R) {j : ℕ} (hj : 1 ≤ j)
    (hjR : (j : ℝ) ≤ R / 2) {x y : E}
    (hx : ‖x‖ ≤ 1 + 1 / (2 * R)) (hy : ‖y‖ ≤ 1 / 4) :
    radialPoint R j x y ∈ ball (0 : E) 1 := by
  let t := (j : ℝ) / R
  have ht : 0 < t := div_pos (by exact_mod_cast (by omega : 0 < j)) hR
  have ht' : t ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith)
  have htl : R⁻¹ ≤ t := by
    simpa [t, one_div] using div_le_div_of_nonneg_right
      (show (1 : ℝ) ≤ j by exact_mod_cast hj) hR.le
  have hhalf : 1 / (2 * R) = R⁻¹ / 2 := by field_simp
  rw [mem_ball_zero_iff]
  calc
    ‖radialPoint R j x y‖ ≤ ‖(1 - t) • x‖ + ‖t • y‖ := norm_add_le _ _
    _ = (1 - t) * ‖x‖ + t * ‖y‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
        abs_of_pos ht]
    _ ≤ (1 - t) * (1 + 1 / (2 * R)) + t * (1 / 4) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (by linarith))
        (mul_le_mul_of_nonneg_left hy ht.le)
    _ ≤ 1 - R⁻¹ / 4 := by
      rw [hhalf]
      nlinarith [mul_nonneg ht.le (inv_nonneg.mpr hR.le)]
    _ < 1 := by have := inv_pos.mpr hR; linarith

/-- A reflected input rescaling gives precisely the original sampling point.
This identity retains the literal radial average when using convolution
(`app:ch_regular_base:eq:extension-radial-formula`). -/
theorem radialPoint_eq_reflected {R : ℝ} (hR : R ≠ 0) {j : ℕ} (hj : j ≠ 0)
    (x y : E) :
    radialPoint R j x y = (-(j : ℝ) / R) • ((1 - R / (j : ℝ)) • x - y) := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  rw [smul_sub, smul_smul]
  have ha : (-(j : ℝ) / R) * (1 - R / (j : ℝ)) = 1 - (j : ℝ) / R := by
    field_simp
    ring
  rw [ha]
  simp [radialPoint, neg_div, neg_smul, sub_eq_add_neg]

/-- The affine frequency in the fixed-kernel convolution costs at most `R`
per derivative, with no dimensional loss
(`app:ch_regular_base:eq:ball-extension-sobolev`). -/
theorem abs_affineFrequency_le {R : ℝ} (hR : 1 ≤ R) {j : ℕ} (hj : 1 ≤ j) :
    |1 - R / (j : ℝ)| ≤ R := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hdiv : R / (j : ℝ) ≤ R := (div_le_iff₀ hj0).mpr
    (by nlinarith [mul_nonneg (by linarith : 0 ≤ R) (sub_nonneg.mpr hj')])
  have hdiv0 : 0 ≤ R / (j : ℝ) := div_nonneg (by linarith) hj0.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end JanetCartan.BallSmoothing
