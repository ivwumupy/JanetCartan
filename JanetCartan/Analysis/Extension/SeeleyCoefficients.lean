module

public import JanetCartan.Analysis.Extension.SeeleyCoefficients.Gaussian
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Universal Seeley extension coefficients

The coefficients at the nodes `-2^k` in the proof of
`app:ch_regular_base:lem:ball-extension` of `paper.tex`. They are limits of the
finite Lagrange coefficients, have Gaussian decay, and reproduce every polynomial
moment at one. In particular all the moment series converge absolutely.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Topology

namespace JanetCartan.Seeley

/-- Absolute moment summability in
`app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem summable_abs_coeff_moment (ℓ : ℕ) :
    Summable (fun k ↦ |coeff k| * (2 : ℝ) ^ (k * ℓ)) := by
  apply ((summable_decay_moment ℓ).mul_left (Real.exp 4)).of_nonneg_of_le
    (fun k ↦ by positivity)
  intro k
  rw [pow_mul]
  simpa only [mul_assoc, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (coeff_bound k) (show 0 ≤ ((2 : ℝ) ^ k) ^ ℓ by positivity)

/-- The signed moment series is absolutely summable
(`app:ch_regular_base:eq:extension-infinite-moments`). -/
theorem summable_coeff_moment (ℓ : ℕ) :
    Summable (fun k ↦ coeff k * node k ^ ℓ) := by
  apply (summable_abs_coeff_moment ℓ).of_norm_bounded
  intro k
  simp [node, norm_mul, norm_pow, Real.norm_eq_abs, pow_mul]

/-- All moments of the limiting coefficients equal one, as asserted in
`app:ch_regular_base:eq:extension-infinite-moments`. -/
theorem infinite_moment (ℓ : ℕ) : ∑' k, coeff k * node k ^ ℓ = 1 := by
  let f : ℕ → ℕ → ℝ := fun N k ↦ if k ≤ N then finiteCoeff N k * node k ^ ℓ else 0
  have hlim (k : ℕ) : Tendsto (fun N ↦ f N k) atTop (𝓝 (coeff k * node k ^ ℓ)) := by
    apply ((tendsto_finiteCoeff k).mul_const (node k ^ ℓ)).congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    simp [f, hN]
  have hbound (N k : ℕ) : ‖f N k‖ ≤ Real.exp 4 * (decay k * ((2 : ℝ) ^ k) ^ ℓ) := by
    simp only [f]
    split_ifs with hk
    · rw [norm_mul, norm_pow]
      have hnode : ‖node k‖ = (2 : ℝ) ^ k := by
        simp [node, norm_pow]
      rw [hnode]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (finiteCoeff_bound hk)
          (show 0 ≤ ((2 : ℝ) ^ k) ^ ℓ by positivity)
    · rw [norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (decay_pos k).le (by positivity))
  have ht := tendsto_tsum_of_dominated_convergence
    ((summable_decay_moment ℓ).mul_left (Real.exp 4)) hlim (Eventually.of_forall hbound)
  have hfinite : ∀ᶠ N in atTop, (∑' k, f N k) = 1 := by
    filter_upwards [eventually_ge_atTop ℓ] with N hN
    rw [tsum_eq_sum (s := range (N + 1)) (fun k hk ↦ by
      simp only [mem_range, not_lt] at hk
      simp [f, show ¬k ≤ N by omega])]
    convert finite_moment N ℓ hN using 1
    apply sum_congr rfl
    intro k hk
    simp [f, show k ≤ N from Nat.le_of_lt_succ (mem_range.mp hk)]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hfinite.mono (fun _ h ↦ h.symm)))

/-- The moment identities together with convergence, in `HasSum` form
(`app:ch_regular_base:eq:extension-infinite-moments`). -/
theorem hasSum_coeff_moment (ℓ : ℕ) : HasSum (fun k ↦ coeff k * node k ^ ℓ) 1 := by
  simpa only [infinite_moment] using (summable_coeff_moment ℓ).hasSum

/-- Existence of universal extension coefficients with all moments and absolute
moment summability (`app:ch_regular_base:eq:extension-infinite-moments`). -/
theorem exists_extension_coefficients :
    ∃ a : ℕ → ℝ, (∀ ℓ : ℕ, HasSum (fun k ↦ a k * (-(2 : ℝ) ^ k) ^ ℓ) 1) ∧
      (∀ ℓ : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ℓ))) :=
  ⟨coeff, hasSum_coeff_moment, summable_abs_coeff_moment⟩

/-- A single existence statement collecting the Gaussian estimate and both moment
assertions from `app:ch_regular_base:lem:ball-extension`. -/
theorem exists_extension_coefficients_with_decay :
    ∃ a : ℕ → ℝ,
      (∀ k, |a k| ≤ Real.exp 8 / (2 : ℝ) ^ (k * (k + 1) / 2)) ∧
      (∀ ℓ : ℕ, HasSum (fun k ↦ a k * (-(2 : ℝ) ^ k) ^ ℓ) 1) ∧
      (∀ ℓ : ℕ, Summable (fun k ↦ |a k| * (2 : ℝ) ^ (k * ℓ))) :=
  ⟨coeff, coeff_triangular_bound, hasSum_coeff_moment, summable_abs_coeff_moment⟩

end JanetCartan.Seeley
