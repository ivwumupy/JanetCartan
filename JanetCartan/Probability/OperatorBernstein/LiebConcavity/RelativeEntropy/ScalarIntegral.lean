module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Scalar resolvent formula for relative entropy

The difference of two shifted reciprocal functions is integrable on `(0,∞)`.
Integrating its logarithmic primitive gives the scalar entropy formula used in
Minsker's Fact 5 and `app:ch_waves:thm:sampling` of `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.OperatorBernstein.LiebConcavity

/-- The logarithmic resolvent primitive tends to zero at infinity
(`app:ch_waves:thm:sampling`). -/
lemma tendsto_log_shift_sub_log_shift (u v : ℝ) :
    Tendsto (fun t : ℝ => Real.log (t + u) - Real.log (t + v)) atTop (𝓝 0) := by
  have hr : Tendsto (fun t : ℝ => 1 + (u - v) / (t + v)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop v tendsto_id))
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  simp only [Real.log_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (max (-u) (-v))] with t ht
  have hu : 0 < t + u := by have := (le_max_left (-u) (-v)).trans_lt ht; linarith
  have hv : 0 < t + v := by have := (le_max_right (-u) (-v)).trans_lt ht; linarith
  change Real.log (1 + (u - v) / (t + v)) = _
  rw [← Real.log_div hu.ne' hv.ne']
  congr 1
  field_simp [hv.ne']
  ring

/-- Derivative of the scalar logarithmic resolvent primitive
(`app:ch_waves:thm:sampling`). -/
lemma hasDerivAt_log_shift_sub_log_shift {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => Real.log (t + u) - Real.log (t + v))
      ((t + u)⁻¹ - (t + v)⁻¹) t := by
  convert!
    (((hasDerivAt_id t).add_const u).log (ne_of_gt (add_pos_of_nonneg_of_pos ht hu))).sub
      (((hasDerivAt_id t).add_const v).log (ne_of_gt (add_pos_of_nonneg_of_pos ht hv))) using 1
  simp [one_div]

/-- The shifted reciprocal difference is absolutely integrable on the positive
half-line (`app:ch_waves:thm:sampling`). -/
lemma integrableOn_inv_shift_sub_inv_shift {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (fun t : ℝ => (t + u)⁻¹ - (t + v)⁻¹) (Ioi 0) := by
  rcases le_total u v with huv | hvu
  · apply integrableOn_Ioi_deriv_of_nonneg'
      (fun t ht => hasDerivAt_log_shift_sub_log_shift hu hv ht)
      _ (tendsto_log_shift_sub_log_shift u v)
    intro t ht
    exact sub_nonneg.mpr (inv_anti₀ (add_pos ht hu) (by linarith))
  · apply integrableOn_Ioi_deriv_of_nonpos'
      (fun t ht => hasDerivAt_log_shift_sub_log_shift hu hv ht)
      _ (tendsto_log_shift_sub_log_shift u v)
    intro t ht
    exact sub_nonpos.mpr (inv_anti₀ (add_pos ht hv) (by linarith))

/-- Integrating the difference of shifted reciprocals recovers a logarithmic
difference (`app:ch_waves:thm:sampling`). -/
lemma integral_inv_shift_sub_inv_shift {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t : ℝ in Ioi 0, ((t + u)⁻¹ - (t + v)⁻¹)) = Real.log v - Real.log u := by
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_log_shift_sub_log_shift hu hv ht)
    (integrableOn_inv_shift_sub_inv_shift hu hv) (tendsto_log_shift_sub_log_shift u v)

/-- Rewriting the scalar entropy integrand as a shifted reciprocal difference
(`app:ch_waves:thm:sampling`). -/
lemma scalarEntropyResolvent_eq {x a t : ℝ} (hx : 0 < x) (ha : 0 < a) (ht : 0 ≤ t) :
    x ^ 2 / (a + t * x) - x / (1 + t) =
      x * ((t + a / x)⁻¹ - (t + 1)⁻¹) := by
  have h₁ : a + t * x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ha (mul_nonneg ht hx.le))
  have h₂ : t + a / x ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ht (div_pos ha hx))
  have h₃ : t + 1 ≠ 0 := by positivity
  have h₄ : 1 + t ≠ 0 := by positivity
  field_simp
  ring

/-- Integrability of the scalar entropy resolvent for arbitrary positive inputs
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma integrableOn_scalarEntropyResolvent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => x ^ 2 / (a + t * x) - x / (1 + t)) (Ioi 0) := by
  apply IntegrableOn.congr_fun ((integrableOn_inv_shift_sub_inv_shift (div_pos ha hx) zero_lt_one).const_mul x)
    _ measurableSet_Ioi
  intro t ht
  exact (scalarEntropyResolvent_eq hx ha ht.le).symm

/-- The scalar resolvent formula for unnormalized relative entropy
(`app:ch_waves:thm:sampling`, Minsker Fact 5). -/
lemma integral_scalarEntropyResolvent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, (x ^ 2 / (a + t * x) - x / (1 + t))) =
      x * (Real.log x - Real.log a) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, x * ((t + a / x)⁻¹ - (t + 1)⁻¹) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => scalarEntropyResolvent_eq hx ha ht.le
    _ = x * (Real.log 1 - Real.log (a / x)) := by
      rw [integral_const_mul, integral_inv_shift_sub_inv_shift (div_pos ha hx) zero_lt_one]
    _ = _ := by rw [Real.log_one, Real.log_div ha.ne' hx.ne']; ring

end JanetCartan.OperatorBernstein.LiebConcavity
