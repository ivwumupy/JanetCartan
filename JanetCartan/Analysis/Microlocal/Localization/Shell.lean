module

public import JanetCartan.Analysis.Microlocal.Localization.RadialIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The negative Sobolev annular split

The Fourier-side split in `app:ch_osc:eq:osc-source-negative`. Only vanishing of
the cutoff below its inner radius is needed. The L² integrability hypotheses
are explicit; deriving the source L² bound and identifying its Fourier
transform remain separate analytic obligations.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.Localization

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- `app:ch_osc:eq:osc-source-negative`: Above the inner radius `cρ`, the negative Sobolev weight
is at most `(cρ) ^ (-2M)`. -/
theorem negativeSobolevWeight_le_of_innerRadius {c ρ M : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hM : 0 ≤ M)
    {x : E} (hx : c * ρ ≤ ‖x‖) :
    (1 + ‖x‖ ^ 2) ^ (-M) ≤ (c * ρ) ^ (-2 * M) := by
  have hb : (c * ρ) ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
    have h := pow_le_pow_left₀ (mul_pos hc hρ).le hx 2
    linarith
  calc
    _ ≤ ((c * ρ) ^ 2) ^ (-M) := Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    _ = _ := by
      rw [← Real.rpow_natCast (c * ρ), ← Real.rpow_mul (by positivity : 0 ≤ c * ρ)]
      congr 1
      ring

/-- `app:ch_osc:eq:osc-source-negative`: Below the inner radius the complementary multiplier
equals one; above it the Sobolev weight gives the gain. -/
theorem negativeSobolevEnergy_le_annular_split {c ρ M : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (π : E → ℂ) (H : E → F) (hπ : ∀ x, ‖x‖ < c * ρ → π x = 0) (x : E) :
    (1 + ‖x‖ ^ 2) ^ (-M) * ‖H x‖ ^ 2 ≤
      (c * ρ) ^ (-2 * M) * ‖H x‖ ^ 2 + ‖(1 - π x) • H x‖ ^ 2 := by
  by_cases hx : c * ρ ≤ ‖x‖
  · exact (mul_le_mul_of_nonneg_right (negativeSobolevWeight_le_of_innerRadius hc hρ hM hx) (sq_nonneg _)).trans
      (le_add_of_nonneg_right (sq_nonneg _))
  · have hw : (1 + ‖x‖ ^ 2) ^ (-M) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖]) (by linarith)
    rw [hπ x (lt_of_not_ge hx), sub_zero, one_smul]
    calc
      _ ≤ ‖H x‖ ^ 2 := by simpa using mul_le_mul_of_nonneg_right hw (sq_nonneg ‖H x‖)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- `app:ch_osc:eq:osc-source-negative`: The source and complementary tail L² bounds justify the
negative Sobolev integral. -/
theorem integrable_negativeSobolevEnergy {c ρ M : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (π : E → ℂ) (H : E → F) (hπ : ∀ x, ‖x‖ < c * ρ → π x = 0)
    (hH : Integrable (fun x ↦ ‖H x‖ ^ 2) μ)
    (ht : Integrable (fun x ↦ ‖(1 - π x) • H x‖ ^ 2) μ) :
    Integrable (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-M) * ‖H x‖ ^ 2) μ := by
  have hw : Continuous (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-M)) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const (fun x ↦ Or.inl (show (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 by positivity))
  apply ((hH.const_mul ((c * ρ) ^ (-2 * M))).add ht).mono'
    (hw.aestronglyMeasurable.mul hH.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(1 + ‖x‖ ^ 2) ^ (-M) * ‖H x‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact negativeSobolevEnergy_le_annular_split hc hρ hM π H hπ x

/-- `app:ch_osc:eq:osc-source-negative`: The negative weighted norm is at most `(cρ) ^ (-M)` times
the source L² norm plus the complementary L² tail. This proves the spectral split; it does not
assume the split inequality. -/
theorem fourierWeightedL2Norm_negative_le_annular_split {c ρ M : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (π : E → ℂ) (H : E → F) (hπ : ∀ x, ‖x‖ < c * ρ → π x = 0)
    (hH : Integrable (fun x ↦ ‖H x‖ ^ 2) μ)
    (ht : Integrable (fun x ↦ ‖(1 - π x) • H x‖ ^ 2) μ) :
    fourierWeightedL2Norm μ (-M) H ≤
      (c * ρ) ^ (-M) * fourierWeightedL2Norm μ 0 H +
        fourierWeightedL2Norm μ 0 (fun x ↦ (1 - π x) • H x) := by
  have hi := integral_mono (integrable_negativeSobolevEnergy hc hρ hM π H hπ hH ht)
    ((hH.const_mul ((c * ρ) ^ (-2 * M))).add ht) (negativeSobolevEnergy_le_annular_split hc hρ hM π H hπ)
  simp only [Pi.add_apply] at hi
  rw [integral_add (hH.const_mul _) ht, integral_const_mul] at hi
  simp only [fourierWeightedL2Norm, Real.rpow_zero, one_mul]
  apply (Real.sqrt_le_sqrt hi).trans
  have hsum (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv,
      mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)]
  apply (hsum _ _ (mul_nonneg (by positivity)
    (integral_nonneg (fun _ ↦ sq_nonneg _)))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).trans_eq
  rw [Real.sqrt_mul (by positivity)]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ c * ρ)]
  congr 1
  ring

end JanetCartan.Localization
