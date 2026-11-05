module

public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# Baseline-one interpolation profiles

Actual closed-ball interpolation yields the power bounds used for the
flow forcing in `app:ch_regular_base:lem:buffered-interpolation` of paper.tex.
The constants are chosen before the function and depend only on the order,
ball, and fixed first-order bound.
-/

public section

open scoped ContDiff

namespace JanetCartan.FlowForcing

open CompositionBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: actual baseline-one
interpolation on a closed ball, with both endpoint orders included. -/
theorem exists_cNorm_baseline_one_profile_closedBall (x : E) {ρ : ℝ}
    (hρ : 0 < ρ) {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) 1 f ≤ M →
      cNorm (Metric.closedBall x ρ) j f ≤
        K * (1 + cNorm (Metric.closedBall x ρ) n f) ^ (((j : ℝ) - 1) / (n - 1)) := by
  let s := Metric.closedBall x ρ
  have hn' : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hj1 : j = 1
  · subst j
    refine ⟨1 + M, by linarith, ?_⟩
    intro f _ hfM
    simpa only [Nat.cast_one, sub_self, zero_div, Real.rpow_zero, mul_one] using
      hfM.trans (show M ≤ 1 + M by linarith)
  by_cases hjeq : j = n
  · subst j
    refine ⟨1, le_rfl, ?_⟩
    intro f _ _
    rw [div_self hn'.ne', Real.rpow_one, one_mul]
    linarith
  have hj' : 1 < j := by omega
  have hjn' : j < n := by omega
  obtain ⟨C, hC, hinterp⟩ := cNorm_le_interpolation_closedBall (F := F) x hρ hj' hjn'
  refine ⟨1 + C * (1 + M), by nlinarith [mul_nonneg hC.le hM], ?_⟩
  intro f hf hfM
  have hθ0 : 0 ≤ ((j : ℝ) - 1) / (n - 1) :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hj)) hn'.le
  have hθ1 : ((j : ℝ) - 1) / (n - 1) ≤ 1 := by
    apply (div_le_one hn').mpr
    exact sub_le_sub_right (by exact_mod_cast hjn) 1
  have hlow : (cNorm s 1 f) ^ (1 - ((j : ℝ) - 1) / (n - 1)) ≤ 1 + M := by
    calc
      _ ≤ (1 + M) ^ (1 - ((j : ℝ) - 1) / (n - 1)) :=
        Real.rpow_le_rpow (cNorm_nonneg s 1 f) (by linarith) (by linarith)
      _ ≤ (1 + M) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  have hhigh : (cNorm s n f) ^ (((j : ℝ) - 1) / (n - 1)) ≤
      (1 + cNorm s n f) ^ (((j : ℝ) - 1) / (n - 1)) :=
    Real.rpow_le_rpow (cNorm_nonneg s n f) (by linarith) hθ0
  have hi := hinterp f hf
  simp only [Nat.cast_one] at hi
  apply hi.trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hlow hC.le) hhigh
    (Real.rpow_nonneg (cNorm_nonneg s n f) _) (by positivity)).trans
  exact mul_le_mul_of_nonneg_right (by linarith)
    (Real.rpow_nonneg (by linarith [cNorm_nonneg s n f]) _)

/-- `app:ch_regular_base:lem:buffered-interpolation`: one constant controls
all the baseline-one power profiles through the fixed top order. No power
profile is assumed: each is supplied by closed-ball interpolation. -/
theorem exists_uniform_cNorm_baseline_one_profile_closedBall (x : E) {ρ : ℝ}
    (hρ : 0 < ρ) {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ f : E → F, ContDiff ℝ ∞ f →
      cNorm (Metric.closedBall x ρ) 1 f ≤ M → ∀ j, 1 ≤ j → j ≤ n →
      cNorm (Metric.closedBall x ρ) j f ≤
        K * (1 + cNorm (Metric.closedBall x ρ) n f) ^ (((j : ℝ) - 1) / (n - 1)) := by
  classical
  have hconstants : ∀ j : Fin (n + 1), ∃ K : ℝ, 1 ≤ K ∧
      ∀ f : E → F, ContDiff ℝ ∞ f → cNorm (Metric.closedBall x ρ) 1 f ≤ M →
      1 ≤ j.val → cNorm (Metric.closedBall x ρ) j f ≤
        K * (1 + cNorm (Metric.closedBall x ρ) n f) ^ (((j.val : ℝ) - 1) / (n - 1)) := by
    intro j
    by_cases hj : 1 ≤ j.val
    · obtain ⟨K, hK, hb⟩ := exists_cNorm_baseline_one_profile_closedBall
        (F := F) x hρ hn hj (Nat.le_of_lt_succ j.isLt) hM
      exact ⟨K, hK, fun f hf hfM _ ↦ hb f hf hfM⟩
    · exact ⟨1, le_rfl, fun _ _ _ h ↦ (hj h).elim⟩
  choose K hK hb using hconstants
  refine ⟨1 + ∑ j, K j, ?_, ?_⟩
  · linarith [Finset.sum_nonneg (fun j _ ↦ (zero_le_one.trans (hK j)))
      (s := Finset.univ)]
  intro f hf hfM j hj hjn
  let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hjn⟩
  have hKi : K i ≤ 1 + ∑ a, K a := by
    have := Finset.single_le_sum (fun a _ ↦ zero_le_one.trans (hK a)) (Finset.mem_univ i)
    linarith
  exact (hb i f hf hfM hj).trans (mul_le_mul_of_nonneg_right hKi
    (Real.rpow_nonneg (by linarith [cNorm_nonneg (Metric.closedBall x ρ) n f]) _))

end JanetCartan.FlowForcing
