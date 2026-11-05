module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # The sampling scale and stretched exponential error

Scalar estimates used in `app:ch_waves:thm:sampling`, especially the passage
from the operator Bernstein bound to `app:ch_waves:eq:sampling-all-prefixes`.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.Sampling

/-- The three-dimensional sampling mesh in `app:ch_waves:thm:sampling`. -/
def samplingMesh (ε Λ : ℝ) : ℝ := Λ ^ (-(1 + ε) / 3)

/-- The error tolerance in `app:ch_waves:eq:sampling-all-prefixes`. -/
def samplingTolerance (ε Λ : ℝ) : ℝ := Λ ^ (-ε / 4)

/-- `app:ch_waves:thm:sampling`: the chosen mesh gives `Λ h³ = Λ⁻ᵋ`. -/
theorem mul_samplingMesh_cube {Λ : ℝ} (hΛ : 0 < Λ) (ε : ℝ) :
    Λ * samplingMesh ε Λ ^ 3 = Λ ^ (-ε) := by
  unfold samplingMesh
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
  calc
    Λ * Λ ^ (-(1 + ε) / 3 * (3 : ℕ)) = Λ ^ (1 + -(1 + ε) / 3 * 3) := by
      rw [Real.rpow_add hΛ, Real.rpow_one]
      norm_num
    _ = Λ ^ (-ε) := by congr 1; ring

/-- `app:ch_waves:thm:sampling`: the inverse mesh volume equals `Λ^(1+ε)`. -/
theorem samplingMesh_inv_cube {Λ : ℝ} (hΛ : 0 < Λ) (ε : ℝ) :
    (samplingMesh ε Λ ^ 3)⁻¹ = Λ ^ (1 + ε) := by
  unfold samplingMesh
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le, ← Real.rpow_neg hΛ.le]
  congr 1
  ring

/-- `app:ch_waves:thm:sampling`: every polynomial is dominated by the
stretched exponential. The polynomial exponent is allowed to be any real number. -/
theorem tendsto_polynomial_mul_exp_neg_rpow (C p c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    Tendsto (fun Λ : ℝ => C * Λ ^ p * Real.exp (-c * Λ ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / a) c hc).comp
    (tendsto_rpow_atTop ha)
  have hh := h.const_mul C
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  dsimp only [Function.comp_def]
  have he : a * (p / a) = p := by field_simp
  rw [← Real.rpow_mul hΛ.le, he]
  ring

/-- `app:ch_waves:thm:sampling`: precisely the stated all-prefix failure bound tends to zero. -/
theorem tendsto_sampling_failure_bound (C c ε : ℝ) (n : ℕ)
    (hc : 0 < c) (hε : 0 < ε) :
    Tendsto (fun Λ : ℝ => C * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)))
      atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using
    tendsto_polynomial_mul_exp_neg_rpow C (↑(n + 1)) c (ε / 2) hc (by positivity)

/-- `app:ch_waves:thm:sampling`: the tolerance determines the block scale. -/
theorem samplingTolerance_fourth {Λ : ℝ} (hΛ : 0 < Λ) (ε : ℝ) :
    samplingTolerance ε Λ ^ 4 = Λ ^ (-ε) := by
  unfold samplingTolerance
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
  congr 1
  norm_num

/-- `app:ch_waves:thm:sampling`: the inverse squared tolerance is the
stretched exponential power. -/
theorem samplingTolerance_sq_mul_rpow {Λ : ℝ} (hΛ : 0 < Λ) (ε : ℝ) :
    samplingTolerance ε Λ ^ 2 * Λ ^ (ε / 2) = 1 := by
  unfold samplingTolerance
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le, ← Real.rpow_add hΛ]
  convert Real.rpow_zero Λ using 1
  congr 1
  norm_num
  ring

/-- `app:ch_waves:thm:sampling`: for `R = A Λ h³` and `v = B R`, the
Bernstein threshold eventually holds and its exponent dominates `c Λ^(ε/2)`.
The constants `A` and `B` are strictly positive upper-bound constants; actual
variance may be zero. -/
theorem eventually_sampling_bernstein_scale {A B ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Λ : ℝ in atTop,
      let t := samplingTolerance ε Λ
      let R := A * (Λ * samplingMesh ε Λ ^ 3)
      let v := B * R
      0 < t ∧ 0 < v ∧ v + R * t / 3 ≤ t ^ 2 ∧
        c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (v + R * t / 3)) := by
  let D := A * (B + 1 / 3)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨(2 * D)⁻¹, by positivity, ?_⟩
  have htend : Tendsto (samplingTolerance ε) atTop (𝓝 0) := by
    change Tendsto (fun Λ : ℝ => Λ ^ (-ε / 4)) atTop (𝓝 0)
    simpa only [neg_div] using
      tendsto_rpow_neg_atTop (show 0 < ε / 4 by positivity)
  have hsmall : ∀ᶠ Λ : ℝ in atTop, D * samplingTolerance ε Λ ^ 2 ≤ 1 := by
    have hh := ((htend.pow 2).const_mul D).eventually
      (eventually_lt_nhds (show D * (0 : ℝ) ^ 2 < 1 by simp))
    exact hh.mono fun _ h => h.le
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with Λ hΛ hs
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let t := samplingTolerance ε Λ
  have ht : 0 < t := Real.rpow_pos_of_pos hΛpos _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  have hR : A * (Λ * samplingMesh ε Λ ^ 3) = A * t ^ 4 := by
    rw [mul_samplingMesh_cube hΛpos, ← samplingTolerance_fourth hΛpos ε]
  dsimp only
  rw [hR]
  change 0 < t ∧ 0 < B * (A * t ^ 4) ∧ _
  let d := B * (A * t ^ 4) + A * t ^ 4 * t / 3
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hd : d ≤ D * t ^ 4 := by
    have := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ A * t ^ 4 / 3 by positivity)
    dsimp [d, D]
    nlinarith
  refine ⟨ht, by positivity, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
    change d ≤ t ^ 2
    change D * t ^ 2 * t ^ 2 ≤ 1 * t ^ 2 at hh
    nlinarith
  · have hi : Λ ^ (ε / 2) = 1 / t ^ 2 := by
      apply (eq_div_iff (pow_ne_zero _ ht.ne')).2
      simpa only [mul_comm] using samplingTolerance_sq_mul_rpow hΛpos ε
    change (2 * D)⁻¹ * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * d)
    apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
    rw [hi]
    calc
      (2 * D)⁻¹ * (1 / t ^ 2) * (2 * d) ≤
          (2 * D)⁻¹ * (1 / t ^ 2) * (2 * (D * t ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (by norm_num))
          (by positivity)
      _ = t ^ 2 := by field_simp

end JanetCartan.Sampling
