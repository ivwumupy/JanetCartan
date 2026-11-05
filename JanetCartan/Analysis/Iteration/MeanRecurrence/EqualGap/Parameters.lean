module

public import JanetCartan.Analysis.Iteration.MeanRecurrence.Precision
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equal-gap cutoffs for the finite mean

The parameters in the proof of `main:lem:mean-recurrence` of paper.tex.
These supply the scalar cutoff choices for `MeanRecurrence.finite_mean_bounds`
and the sampled current-mean construction.
-/

@[expose] public noncomputable section

namespace JanetCartan.MeanRecurrence.EqualGap

/-- `main:lem:mean-recurrence`: the gap `(d_f - d_in)/(I+1)`. -/
def gap (dIn dFinal : ℝ) (I : ℕ) : ℝ := (dFinal - dIn) / (I + 1)

/-- `main:lem:mean-recurrence`: the exponent `d_l = d_in + (l+1)Δ`. -/
def exponent (dIn dFinal : ℝ) (I l : ℕ) : ℝ :=
  dIn + (l + 1) * gap dIn dFinal I

/-- `main:lem:mean-recurrence`: the precise dyadic cutoff, using integer ceiling. -/
def cutoff (H dIn dFinal : ℝ) (I l : ℕ) : ℝ :=
  (2 : ℝ) ^ ⌈Real.logb 2 (H ^ exponent dIn dFinal I l)⌉

/-- `main:lem:mean-recurrence`: there is a positive gap whenever `d_in < d_f`. -/
theorem gap_pos {dIn dFinal : ℝ} (h : dIn < dFinal) (I : ℕ) :
    0 < gap dIn dFinal I := by
  exact div_pos (sub_pos.mpr h) (by positivity)

/-- `main:lem:mean-recurrence`: the unused last gap separates every cutoff
exponent from `d_f`. -/
theorem exponent_add_gap_le {dIn dFinal : ℝ} (h : dIn < dFinal)
    {I l : ℕ} (hl : l < I) :
    exponent dIn dFinal I l + gap dIn dFinal I ≤ dFinal := by
  have hg := (gap_pos h I).le
  have heq : ((I : ℝ) + 1) * gap dIn dFinal I = dFinal - dIn := by
    unfold gap
    exact mul_div_cancel₀ _ (by positivity)
  have hl' : (l : ℝ) + 1 ≤ I := by exact_mod_cast hl
  dsimp only [exponent]
  nlinarith [mul_le_mul_of_nonneg_right hl' hg]

/-- `main:lem:mean-recurrence`: ceiling a base-two logarithm changes the
band scale by at most a factor two. -/
theorem cutoff_bounds {H : ℝ} (hH : 0 < H) (dIn dFinal : ℝ) (I l : ℕ) :
    H ^ exponent dIn dFinal I l ≤ cutoff H dIn dFinal I l ∧
      cutoff H dIn dFinal I l ≤ 2 * H ^ exponent dIn dFinal I l := by
  let x := H ^ exponent dIn dFinal I l
  have hx : 0 < x := Real.rpow_pos_of_pos hH _
  have hlog : (2 : ℝ) ^ Real.logb 2 x = x := Real.rpow_logb (by norm_num)
    (by norm_num) hx
  change x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉ ∧ (2 : ℝ) ^ ⌈Real.logb 2 x⌉ ≤ 2 * x
  simp only [← Real.rpow_intCast]
  constructor
  · exact hlog.symm.trans_le
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _))
  · calc
      _ ≤ (2 : ℝ) ^ (Real.logb 2 x + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.ceil_lt_add_one _).le
      _ = 2 * x := by rw [Real.rpow_add (by norm_num), hlog, Real.rpow_one, mul_comm]

/-- `main:lem:mean-recurrence`: an explicit common threshold for all bands. -/
def threshold (dIn dFinal : ℝ) (I : ℕ) : ℝ :=
  max 2 ((3 : ℝ) ^ (gap dIn dFinal I)⁻¹)

/-- `main:lem:mean-recurrence`: at the fixed threshold, even twice each
unrounded scale lies strictly below `H^d_f`. -/
theorem twice_scale_lt_final {dIn dFinal H : ℝ} (h : dIn < dFinal)
    {I l : ℕ} (hl : l < I) (hH : threshold dIn dFinal I ≤ H) :
    2 * H ^ exponent dIn dFinal I l < H ^ dFinal := by
  have hg := gap_pos h I
  have hHtwo : 2 ≤ H := (le_max_left ..).trans hH
  have hHpos : 0 < H := by linarith
  have hthree : 3 ≤ H ^ gap dIn dFinal I := by
    calc
      3 = ((3 : ℝ) ^ (gap dIn dFinal I)⁻¹) ^ gap dIn dFinal I := by
        rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ hg.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) ((le_max_right ..).trans hH) hg.le
  calc
    _ < H ^ exponent dIn dFinal I l * H ^ gap dIn dFinal I := by
      have := Real.rpow_pos_of_pos hHpos (exponent dIn dFinal I l)
      nlinarith
    _ = H ^ (exponent dIn dFinal I l + gap dIn dFinal I) :=
      (Real.rpow_add hHpos _ _).symm
    _ ≤ H ^ dFinal := Real.rpow_le_rpow_of_exponent_le (by linarith)
      (exponent_add_gap_le h hl)

/-- `main:lem:mean-recurrence`: the dyadic bands all lie below the final band. -/
theorem cutoff_lt_final {dIn dFinal H : ℝ} (h : dIn < dFinal)
    {I l : ℕ} (hl : l < I) (hH : threshold dIn dFinal I ≤ H) :
    cutoff H dIn dFinal I l < H ^ dFinal := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left ..).trans hH)
  exact (cutoff_bounds hHpos dIn dFinal I l).2.trans_lt (twice_scale_lt_final h hl hH)

/-- `main:lem:mean-recurrence`: a finite integer order satisfying the strict
tail requirement. No derivative order is assumed to be infinite. -/
def tailOrder (dIn dFinal γ : ℝ) (I : ℕ) : ℕ :=
  ⌊(dFinal / 2 + 2 * γ + 1) / gap dIn dFinal I⌋₊ + 1

/-- `main:lem:mean-recurrence`: the chosen finite order has the required gap. -/
theorem tailOrder_spec {dIn dFinal : ℝ} (h : dIn < dFinal) (γ : ℝ) (I : ℕ) :
    dFinal / 2 + 2 * γ + 1 < gap dIn dFinal I * tailOrder dIn dFinal γ I := by
  have hg := gap_pos h I
  have hs := (div_lt_iff₀ hg).mp
    (Nat.lt_floor_add_one ((dFinal / 2 + 2 * γ + 1) / gap dIn dFinal I))
  simpa only [tailOrder, Nat.cast_add, Nat.cast_one, mul_comm] using hs

end JanetCartan.MeanRecurrence.EqualGap
