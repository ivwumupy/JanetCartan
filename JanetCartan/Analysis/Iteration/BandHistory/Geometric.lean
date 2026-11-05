module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Numerical estimates for band-limited histories

The geometric-series argument in `main:lem:history`. These results are numerical:
no Bernstein inequality or regularity of a periodic field is assumed implicitly.
-/

@[expose] public noncomputable section

open Filter Topology

namespace JanetCartan

/-- The stage scale `R_j = R₀^(v^j)` in `main:lem:history`. -/
def historyScale (R v : ℝ) (j : ℕ) : ℝ := R ^ (v ^ j)

/-- The explicit geometric majorant in the proof of `main:lem:history`. -/
def historyBound (C R v μ : ℝ) : ℝ :=
  C * R ^ (-μ) / (1 - R ^ (-μ * (v - 1)))

/-- `main:lem:history`: the supergeometric decay is bounded by a geometric sequence. -/
theorem historyScale_neg_pow_le_geometric {R v μ : ℝ}
    (hR : 1 ≤ R) (hv : 1 ≤ v) (hμ : 0 ≤ μ) (i : ℕ) :
    historyScale R v i ^ (-μ) ≤
      R ^ (-μ) * (R ^ (-μ * (v - 1))) ^ i := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpow := one_add_mul_sub_le_pow (by linarith : -1 ≤ v) i
  calc
    historyScale R v i ^ (-μ) = R ^ (v ^ i * (-μ)) :=
      (Real.rpow_mul hR0.le _ _).symm
    _ ≤ R ^ (-μ + (-μ * (v - 1)) * (i : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hR
      nlinarith
    _ = R ^ (-μ) * (R ^ (-μ * (v - 1))) ^ i := by
      rw [Real.rpow_add hR0, Real.rpow_mul_natCast hR0.le]

/-- `main:lem:history`: the geometric ratio is strictly below one. -/
theorem history_ratio_lt_one {R v μ : ℝ}
    (hR : 1 < R) (hv : 1 < v) (hμ : 0 < μ) :
    R ^ (-μ * (v - 1)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hR (mul_neg_of_neg_of_pos (neg_neg_of_pos hμ)
    (sub_pos.mpr hv))

/-- `main:lem:history`: any nonnegative sequence with the stated decay is summable. -/
theorem summable_of_history_bound {a : ℕ → ℝ} {C R v μ : ℝ}
    (hR : 1 < R) (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i)
    (hbound : ∀ i, a i ≤ C * historyScale R v i ^ (-μ)) : Summable a := by
  have hgeom := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by linarith : 0 ≤ R) _) (history_ratio_lt_one hR hv hμ)).mul_left
      (C * R ^ (-μ))
  refine Summable.of_nonneg_of_le ha (fun i ↦ ?_) hgeom
  calc
    a i ≤ C * historyScale R v i ^ (-μ) := hbound i
    _ ≤ C * (R ^ (-μ) * (R ^ (-μ * (v - 1))) ^ i) :=
      mul_le_mul_of_nonneg_left (historyScale_neg_pow_le_geometric hR.le hv.le hμ.le i) hC
    _ = (C * R ^ (-μ)) * (R ^ (-μ * (v - 1))) ^ i := (mul_assoc _ _ _).symm

/-- `main:lem:history`: the full sum satisfies the manuscript's explicit bound. -/
theorem tsum_le_historyBound {a : ℕ → ℝ} {C R v μ : ℝ}
    (hR : 1 < R) (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i)
    (hbound : ∀ i, a i ≤ C * historyScale R v i ^ (-μ)) :
    ∑' i, a i ≤ historyBound C R v μ := by
  have hratio := history_ratio_lt_one hR hv hμ
  have hnonneg := Real.rpow_nonneg (by linarith : 0 ≤ R) (-μ * (v - 1))
  have hgeom := (summable_geometric_of_lt_one hnonneg hratio).mul_left (C * R ^ (-μ))
  calc
    ∑' i, a i ≤ ∑' i : ℕ, (C * R ^ (-μ)) * (R ^ (-μ * (v - 1))) ^ i := by
      apply (summable_of_history_bound hR hv hμ hC ha hbound).tsum_le_tsum _ hgeom
      intro i
      calc
        a i ≤ C * historyScale R v i ^ (-μ) := hbound i
        _ ≤ C * (R ^ (-μ) * (R ^ (-μ * (v - 1))) ^ i) :=
          mul_le_mul_of_nonneg_left
            (historyScale_neg_pow_le_geometric hR.le hv.le hμ.le i) hC
        _ = _ := (mul_assoc _ _ _).symm
    _ = historyBound C R v μ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hnonneg hratio]
      rfl

/-- `main:eq:total-small`: the explicit bound tends to zero as the initial scale grows. -/
theorem tendsto_historyBound (C : ℝ) {v μ : ℝ} (hv : 1 < v) (hμ : 0 < μ) :
    Tendsto (fun R ↦ historyBound C R v μ) atTop (𝓝 0) := by
  have hnum := (tendsto_const_nhds (x := C)).mul (tendsto_rpow_neg_atTop hμ)
  have hratio : Tendsto (fun R : ℝ ↦ R ^ (-μ * (v - 1))) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (mul_pos hμ (sub_pos.mpr hv))
  simpa only [mul_zero, sub_zero, zero_div, historyBound, Pi.div_def] using
    hnum.div (tendsto_const_nhds.sub hratio) (by norm_num : (1 : ℝ) - 0 ≠ 0)

/-- `main:eq:total-small`: uniform decay bounds imply smallness of the total history. -/
theorem tendsto_tsum_of_history_bound {a : ℝ → ℕ → ℝ} {C v μ : ℝ}
    (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (ha : ∀ R, 2 ≤ R → ∀ i, 0 ≤ a R i)
    (hbound : ∀ R, 2 ≤ R → ∀ i, a R i ≤ C * historyScale R v i ^ (-μ)) :
    Tendsto (fun R ↦ ∑' i, a R i) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_historyBound C hv hμ)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact tsum_nonneg (ha R hR)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact tsum_le_historyBound (by linarith) hv hμ hC (ha R hR) (hbound R hR)

/-- `main:lem:history`: enlarging `R₀` decreases each decaying term. -/
theorem historyScale_neg_pow_antitone {R S v μ : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) (hv : 0 ≤ v) (hμ : 0 ≤ μ) (i : ℕ) :
    historyScale S v i ^ (-μ) ≤ historyScale R v i ^ (-μ) := by
  apply Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hR _) _ (neg_nonpos.mpr hμ)
  exact Real.rpow_le_rpow hR.le hRS (pow_nonneg hv i)

/-- `main:lem:history`: finite sums have a bound independent of their length and `R₀ ≥ 2`. -/
theorem sum_le_historyBound_two {a : ℕ → ℝ} {C R v μ : ℝ}
    (hR : 2 ≤ R) (hv : 1 < v) (hμ : 0 < μ) (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i)
    (hbound : ∀ i, a i ≤ C * historyScale R v i ^ (-μ)) (s : Finset ℕ) :
    ∑ i ∈ s, a i ≤ historyBound C 2 v μ := by
  have hb : ∀ i, a i ≤ C * historyScale 2 v i ^ (-μ) := fun i ↦
    (hbound i).trans (mul_le_mul_of_nonneg_left
      (historyScale_neg_pow_antitone (by norm_num) hR (by linarith) hμ.le i) hC)
  exact ((summable_of_history_bound (by norm_num) hv hμ hC ha hb).sum_le_tsum
    s (fun i _ ↦ ha i)).trans (tsum_le_historyBound (by norm_num) hv hμ hC ha hb)

/-- `main:lem:history`: every previous band lies below the current coefficient scale. -/
theorem historyScale_band_le {R v b : ℝ} (hR : 1 ≤ R) (hv : 1 ≤ v)
    (hb : 0 ≤ b) {i j : ℕ} (hij : i < j) :
    historyScale R v i ^ b ≤ historyScale R v j ^ (b / v) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  rw [historyScale, historyScale, ← Real.rpow_mul hR0, ← Real.rpow_mul hR0]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hv (Nat.succ_le_of_lt hij)) (div_nonneg hb hv0.le)
  calc
    v ^ i * b = v ^ (i + 1) * (b / v) := by rw [pow_succ]; field_simp
    _ ≤ v ^ j * (b / v) := hp

/-- `main:lem:history`: the coefficient scale is at least one. -/
theorem one_le_historyScale_profile {R v b : ℝ} (hR : 1 ≤ R) (hv : 0 ≤ v)
    (hb : 0 ≤ b) (j : ℕ) : 1 ≤ historyScale R v j ^ (b / v) :=
  Real.one_le_rpow (Real.one_le_rpow hR (pow_nonneg hv j)) (div_nonneg hb hv)

/-- `main:eq:history-current`, numerical part: quantified increment Bernstein estimates
produce the fixed-baseline profile with a constant uniform in the history length and `R₀`.
Here `a i` is the baseline size and `d i` is the size at the requested derivative order. -/
theorem sum_history_profile_le {a d : ℕ → ℝ} {C D R v μ b : ℝ}
    (hR : 2 ≤ R) (hv : 1 < v) (hμ : 0 < μ) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : ∀ i, 0 ≤ a i)
    (hbound : ∀ i, a i ≤ C * historyScale R v i ^ (-μ))
    (r r₀ j : ℕ)
    (hbernstein : ∀ i, i < j →
      d i ≤ D * (historyScale R v i ^ b) ^ (r - r₀) * a i) :
    ∑ i ∈ Finset.range j, d i ≤
      (D * historyBound C 2 v μ) * (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
  have hT : 0 ≤ historyScale R v j ^ (b / v) :=
    Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _
  calc
    ∑ i ∈ Finset.range j, d i ≤
        ∑ i ∈ Finset.range j,
          D * (historyScale R v j ^ (b / v)) ^ (r - r₀) * a i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (hbernstein i (Finset.mem_range.mp hi)).trans
      apply mul_le_mul_of_nonneg_right _ (ha i)
      apply mul_le_mul_of_nonneg_left _ hD
      exact pow_le_pow_left₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)
        (historyScale_band_le (by linarith) hv.le hb (Finset.mem_range.mp hi)) _
    _ = (D * (historyScale R v j ^ (b / v)) ^ (r - r₀)) *
        ∑ i ∈ Finset.range j, a i := (Finset.mul_sum ..).symm
    _ ≤ (D * (historyScale R v j ^ (b / v)) ^ (r - r₀)) * historyBound C 2 v μ :=
      mul_le_mul_of_nonneg_left
        (sum_le_historyBound_two hR hv hμ hC ha hbound _) (mul_nonneg hD (pow_nonneg hT _))
    _ = _ := by ring

/-- `main:eq:history-current`, numerical part: a fixed initial profile is absorbed into
constants independent of `j` and `R₀`. The same bound works for any family sharing `A`. -/
theorem initial_add_sum_history_profile_le {a d : ℕ → ℝ} {A C D R v μ b : ℝ}
    (hR : 2 ≤ R) (hv : 1 < v) (hμ : 0 < μ) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : ∀ i, 0 ≤ a i)
    (hbound : ∀ i, a i ≤ C * historyScale R v i ^ (-μ))
    (r r₀ j : ℕ)
    (hbernstein : ∀ i, i < j →
      d i ≤ D * (historyScale R v i ^ b) ^ (r - r₀) * a i) :
    A + ∑ i ∈ Finset.range j, d i ≤
      (A + D * historyBound C 2 v μ) * (historyScale R v j ^ (b / v)) ^ (r - r₀) := by
  have hT := one_le_pow₀
    (one_le_historyScale_profile (by linarith : 1 ≤ R) (by linarith : 0 ≤ v) hb j)
    (n := r - r₀)
  calc
    A + ∑ i ∈ Finset.range j, d i ≤
        A * (historyScale R v j ^ (b / v)) ^ (r - r₀) +
          (D * historyBound C 2 v μ) * (historyScale R v j ^ (b / v)) ^ (r - r₀) :=
      add_le_add (le_mul_of_one_le_right hA hT)
        (sum_history_profile_le hR hv hμ hb hC hD ha hbound r r₀ j hbernstein)
    _ = _ := by ring

end JanetCartan
