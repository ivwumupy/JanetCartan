module

public import JanetCartan.Iteration.PhysicalMean.Source

/-!
# Finite precision for the fixed-sample source run

The algebraic recurrence is the one in paper-v2, not the old adaptive-cutoff
mean recurrence.  The finite low-norm iteration below keeps the explicit
linear defect, bilinear term and tail separate.  Its analytic producers are
`block-normal`, `mean-quadratic-low` and the same-row sampling/tail comparison.
The numerical precision choice itself has no analytic hypotheses and does not
alter the fixed source order, wave family, sample, or input cutoff.
-/

@[expose] public noncomputable section

namespace JanetCartan.PhysicalMean

section LowNorm

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `new:eq:difference-bound`: iterate the actual fixed-source difference
identity with its separate primitive linear and quadratic estimates.  The tail
is paid only a finite number of times.  No residual bound or successful source
is a premise.  Actual canonical operators still have to supply the two bounds. -/
theorem sourceResidual_norm_le
    (E : Y →ₗ[ℝ] Y) (Q : Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (hQ : ∀ u v, Q u v = Q v u) (g : Y) (J : ℕ)
    {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : 0 ≤ t) (hsmall : a + c ≤ 1)
    (hlinear : ∀ j < J,
      let d := sourceIterate E Q g (j + 1) - sourceIterate E Q g j
      ‖d - E d‖ ≤ a * ‖d‖ + t)
    (hquadratic : ∀ j < J,
      let d := sourceIterate E Q g (j + 1) - sourceIterate E Q g j
      ‖Q d (sourceIterate E Q g (j + 1) + sourceIterate E Q g j)‖ ≤ c * ‖d‖) :
    ‖sourceResidual E Q g (sourceIterate E Q g J)‖ ≤
      (a + c) ^ J * ‖g‖ + (J : ℝ) * t := by
  have hb : 0 ≤ a + c := add_nonneg ha hc
  have hstep (j : ℕ) (hj : j < J) :
      ‖sourceIterate E Q g (j + 2) - sourceIterate E Q g (j + 1)‖ ≤
        (a + c) * ‖sourceIterate E Q g (j + 1) - sourceIterate E Q g j‖ + t := by
    rw [sourceIterate_difference_succ E Q hQ]
    exact ((norm_sub_le _ _).trans (add_le_add (hlinear j hj) (hquadratic j hj))).trans_eq (by ring)
  have hbound : ∀ j ≤ J,
      ‖sourceIterate E Q g (j + 1) - sourceIterate E Q g j‖ ≤
        (a + c) ^ j * ‖g‖ + (j : ℝ) * t := by
    intro j
    induction j with
    | zero => intro _; simp [sourceIterate]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hmul := mul_le_mul_of_nonneg_left hprev hb
      have htj : (a + c) * ((j : ℝ) * t) ≤ (j : ℝ) * t :=
        mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) ht) hsmall
      have hn := hstep j (by omega)
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  rw [sourceResidual_eq_difference]
  exact hbound J le_rfl

end LowNorm

/-- `new:eq:source-bound`: the fixed source order of v2 has the required
strict interpolation gap, and the concentration loss is smaller than β. -/
theorem source_iteration_fixed_gaps (n : ℕ) :
    n < RevisedScales.sourceOrder n ∧
    0 < (1 + samplingSlack - fineExponent) / 4 ∧
    (1 + samplingSlack - fineExponent) / 4 < separationExponent ∧
    0 < fineExponent - 1 := by
  refine ⟨(RevisedScales.source_order_and_forcing_gap n).2.1,
    RevisedScales.concentration_gap.2.1, ?_, ?_⟩
  · norm_num [samplingSlack, fineExponent, meanSlack, separationExponent]
  · norm_num [fineExponent, meanSlack]

/-- Step 5 of `app:ch_mean_pairs:prop:mean-iteration`: choose the finite number
of Picard steps and the PROOF-ONLY tail order before constants, histories or
samples.  The input cutoff remains `K=R^fineExponent`.  This absorbs the exact
interpolation expression into `R^(-accuracy)` and uses no legacy forcing loss. -/
theorem exists_source_iteration_precision (accuracy : ℝ) :
    ∃ J q : ℕ,
      2 * accuracy < ((1 + samplingSlack - fineExponent) / 4) * J ∧
      2 * accuracy < (q : ℝ) * (fineExponent - 1) ∧
      ∀ C : ℝ, 0 ≤ C → ∃ S : ℝ, 2 ≤ S ∧ ∀ R : ℝ, S ≤ R →
        C * R ^ (-separationExponent) *
          Real.sqrt (R ^ (-((1 + samplingSlack - fineExponent) / 4) * J) +
            (R / R ^ fineExponent) ^ q) ≤ R ^ (-accuracy) := by
  let ω := (1 + samplingSlack - fineExponent) / 4
  have hω : 0 < ω := RevisedScales.concentration_gap.2.1
  have hf : 0 < fineExponent - 1 := by norm_num [fineExponent, meanSlack]
  obtain ⟨J, hJ⟩ := exists_nat_gt ((2 * accuracy + 2) / ω)
  obtain ⟨q, hq⟩ := exists_nat_gt ((2 * accuracy + 2) / (fineExponent - 1))
  have hJ' : 2 * accuracy + 2 < ω * J := by
    have := (div_lt_iff₀ hω).mp hJ
    nlinarith
  have hq' : 2 * accuracy + 2 < (q : ℝ) * (fineExponent - 1) :=
    (div_lt_iff₀ hf).mp hq
  refine ⟨J, q, by change 2 * accuracy < ω * J; linarith, by linarith, ?_⟩
  intro C hC
  have hlarge := eventually_mul_rpow_le_of_exponent_lt (2 * C)
    (show -accuracy - 1 < -accuracy by linarith)
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max 2 S, le_max_left _ _, ?_⟩
  intro R hR
  have hRone : 1 ≤ R := by linarith [((le_max_left 2 S).trans hR : (2 : ℝ) ≤ R)]
  have hRp : 0 < R := zero_lt_one.trans_le hRone
  have hpower : (R / R ^ fineExponent) ^ q = R ^ (-(q : ℝ) * (fineExponent - 1)) := by
    have hquot : R / R ^ fineExponent = R ^ (1 - fineExponent) := by
      rw [Real.rpow_sub hRp, Real.rpow_one]
    rw [hquot, ← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  have hfirst : R ^ (-ω * J) ≤ R ^ (-2 * accuracy - 2) :=
    Real.rpow_le_rpow_of_exponent_le hRone (by nlinarith)
  have hsecond : (R / R ^ fineExponent) ^ q ≤ R ^ (-2 * accuracy - 2) := by
    rw [hpower]
    exact Real.rpow_le_rpow_of_exponent_le hRone (by nlinarith)
  have hsqrt : Real.sqrt (R ^ (-ω * J) + (R / R ^ fineExponent) ^ q) ≤
      2 * R ^ (-accuracy - 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have he : (2 * R ^ (-accuracy - 1)) ^ 2 = 4 * R ^ (-2 * accuracy - 2) := by
      rw [mul_pow, pow_two (R ^ _), ← Real.rpow_add hRp]
      congr 1
      · norm_num
      · congr 1; ring
    rw [he]
    linarith [Real.rpow_nonneg hRp.le (-2 * accuracy - 2)]
  have hh : R ^ (-separationExponent) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hRone
    norm_num [separationExponent]
  change C * R ^ (-separationExponent) * Real.sqrt (R ^ (-ω * J) + _) ≤ _
  calc
    _ ≤ C * (2 * R ^ (-accuracy - 1)) := by
      apply (mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hC (by positivity))).trans
      exact mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hh hC)
        (by positivity)
    _ = (2 * C) * R ^ (-accuracy - 1) := by ring
    _ ≤ _ := hS R ((le_max_right _ _).trans hR)

end JanetCartan.PhysicalMean
