module

public import JanetCartan.Analysis.Iteration.MeanRecurrence.EqualGap.Parameters
public import JanetCartan.Analysis.Iteration.MeanRecurrence.Estimates

/-!
# The scalar equal-gap tail estimate

This proves the scalar estimate in `main:lem:mean-recurrence` of paper.tex,
including step zero, with a constant independent of the step count. It supplies
the exponent bookkeeping for the `htail` premise of
`MeanRecurrence.finite_mean_bounds`. Applying the scalar bound to the actual
raw adjoint and cutoff is a separate analytic obligation of the current mean.
-/

@[expose] public noncomputable section

namespace JanetCartan.MeanRecurrence.EqualGap

open Finset

/-- `main:lem:mean-recurrence`: the raw-tail scalar expression is bounded
by `3 H^(-γ(l+1)-1)`, uniformly for `l < I`. The order `S` is any finite
integer with the manuscript's strict gap inequality. -/
theorem tail_le {dIn dFinal γ H : ℝ} {I S l : ℕ}
    (hd : dIn < dFinal) (hdf : 0 ≤ dFinal) (hγ : 0 ≤ γ) (hH : 2 ≤ H)
    (hS : dFinal / 2 + 2 * γ + 1 < gap dIn dFinal I * S) (hl : l < I) :
    H ^ (-((l : ℝ) + 1) * gap dIn dFinal I * S) +
        (∑ i ∈ range l, H ^ (-γ * i - ((l : ℝ) - i) * gap dIn dFinal I * S +
          exponent dIn dFinal I i / 2)) ≤
      3 * H ^ (-γ * ((l : ℝ) + 1) - 1) := by
  have hHpos : 0 < H := by linarith
  have hHone : 1 ≤ H := by linarith
  have hA : γ + 1 ≤ gap dIn dFinal I * S := by linarith
  have hfirst : H ^ (-((l : ℝ) + 1) * gap dIn dFinal I * S) ≤
      H ^ (-γ * ((l : ℝ) + 1) - 1) := by
    apply Real.rpow_le_rpow_of_exponent_le hHone
    nlinarith [mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
      (sub_nonneg.mpr hA)]
  have hratio : 0 ≤ H⁻¹ := inv_nonneg.mpr hHpos.le
  have hhalf : H⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hH
  have hterm (i : ℕ) (hi : i < l) :
      H ^ (-γ * i - ((l : ℝ) - i) * gap dIn dFinal I * S +
        exponent dIn dFinal I i / 2) ≤
      H ^ (-γ * ((l : ℝ) + 1) - 1) * H⁻¹ ^ (l - 1 - i) := by
    have hdi : exponent dIn dFinal I i ≤ dFinal := by
      have := exponent_add_gap_le hd (hi.trans hl)
      have := gap_pos hd I
      linarith
    have hj : ((l - 1 - i : ℕ) : ℝ) = (l : ℝ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    have hjnonneg : 0 ≤ (l : ℝ) - 1 - i := by
      rw [← hj]
      positivity
    calc
      _ ≤ H ^ ((-γ * ((l : ℝ) + 1) - 1) + (-1) * (l - 1 - i : ℕ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hHone
        rw [hj]
        nlinarith [mul_nonneg hjnonneg (sub_nonneg.mpr hA)]
      _ = _ := by
        rw [Real.rpow_add hHpos, Real.rpow_mul_natCast hHpos.le, Real.rpow_neg_one]
  have hsum : (∑ i ∈ range l,
      H ^ (-γ * i - ((l : ℝ) - i) * gap dIn dFinal I * S +
        exponent dIn dFinal I i / 2)) ≤ 2 * H ^ (-γ * ((l : ℝ) + 1) - 1) := by
    calc
      _ ≤ ∑ i ∈ range l, H ^ (-γ * ((l : ℝ) + 1) - 1) * H⁻¹ ^ (l - 1 - i) :=
        sum_le_sum (fun i hi ↦ hterm i (mem_range.mp hi))
      _ = ∑ i ∈ range l, H ^ (-γ * ((l : ℝ) + 1) - 1) * H⁻¹ ^ i :=
        sum_range_reflect (fun i ↦ H ^ (-γ * ((l : ℝ) + 1) - 1) * H⁻¹ ^ i) l
      _ ≤ _ := sum_le_two_mul (Real.rpow_pos_of_pos hHpos _).le hratio hhalf l
        (fun _ _ ↦ le_rfl)
  linarith

/-- `main:lem:mean-recurrence`: explicit finite choices for precision `Q`.
The count is the existing `precisionSteps`; the order and common threshold
are constructed here. All dyadic and scalar-tail estimates hold simultaneously.
This supplies scalar parameters, not the analytic raw-tail bound itself. -/
theorem precision_parameters {dIn dFinal γ : ℝ} (hd : dIn < dFinal)
    (hdf : 0 ≤ dFinal) (hγ : 0 < γ) (Q : ℝ) :
    let I := precisionSteps Q γ
    let S := tailOrder dIn dFinal γ I
    let H₀ := threshold dIn dFinal I
    0 < gap dIn dFinal I ∧
      dFinal / 2 + 2 * γ + 1 < gap dIn dFinal I * S ∧
      2 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H →
        (H ^ (-γ)) ^ I ≤ H ^ (-Q) ∧
        ∀ l < I,
          H ^ exponent dIn dFinal I l ≤ cutoff H dIn dFinal I l ∧
          cutoff H dIn dFinal I l ≤ 2 * H ^ exponent dIn dFinal I l ∧
          2 * H ^ exponent dIn dFinal I l < H ^ dFinal ∧
          H ^ (-((l : ℝ) + 1) * gap dIn dFinal I * S) +
            (∑ i ∈ range l, H ^ (-γ * i - ((l : ℝ) - i) * gap dIn dFinal I * S +
              exponent dIn dFinal I i / 2)) ≤
            3 * H ^ (-γ * ((l : ℝ) + 1) - 1) := by
  dsimp only
  refine ⟨gap_pos hd _, tailOrder_spec hd γ _, le_max_left .., ?_⟩
  intro H hH
  have hHtwo : 2 ≤ H := (le_max_left ..).trans hH
  have hHpos : 0 < H := by linarith
  refine ⟨geometric_precision_of_count (by linarith) hγ, ?_⟩
  intro l hl
  exact ⟨(cutoff_bounds hHpos _ _ _ _).1, (cutoff_bounds hHpos _ _ _ _).2,
    twice_scale_lt_final hd hl hH, tail_le hd hdf hγ.le hHtwo (tailOrder_spec hd γ _) hl⟩

end JanetCartan.MeanRecurrence.EqualGap
