module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite Seeley coefficients

The Lagrange interpolation construction in
`app:ch_regular_base:eq:extension-finite-moments` of `paper.tex`.
-/

@[expose] public noncomputable section

open Finset Polynomial

namespace JanetCartan.Seeley

/-- The negative dyadic nodes in `app:ch_regular_base:lem:ball-extension`. -/
def node (k : ℕ) : ℝ := -(2 : ℝ) ^ k

/-- The finite coefficients from `app:ch_regular_base:eq:extension-finite-moments`.
Only indices `k ≤ N` occur in the interpolation formula. -/
def finiteCoeff (N k : ℕ) : ℝ :=
  ∏ j ∈ (range (N + 1)).erase k, (1 + (2 : ℝ) ^ j) / (2 ^ j - 2 ^ k)

/-- The interpolation nodes of the ball extension are distinct. -/
theorem node_injective : Function.Injective node := by
  intro i j h
  have hpow : (2 : ℝ) ^ i = 2 ^ j := neg_injective h
  exact (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hpow

/-- The product defining a finite coefficient is the Lagrange basis evaluated at one
(`app:ch_regular_base:eq:extension-finite-moments`). -/
theorem finiteCoeff_eq_eval_basis (N k : ℕ) :
    finiteCoeff N k = (Lagrange.basis (range (N + 1)) node k).eval 1 := by
  simp only [finiteCoeff, Lagrange.basis, eval_prod]
  apply prod_congr rfl
  intro j _
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, node]
  rw [div_eq_mul_inv]
  ring

/-- Finite moment identities, exactly
`app:ch_regular_base:eq:extension-finite-moments`. -/
theorem finite_moment (N ℓ : ℕ) (hℓ : ℓ ≤ N) :
    ∑ k ∈ range (N + 1), finiteCoeff N k * node k ^ ℓ = 1 := by
  have hdeg : (X ^ ℓ : ℝ[X]).degree < ↑(#(range (N + 1))) := by
    simp only [degree_X_pow, card_range]
    exact_mod_cast (Nat.lt_succ_of_le hℓ)
  have h := congrArg (fun p : ℝ[X] ↦ p.eval 1)
    (Lagrange.eq_interpolate node_injective.injOn hdeg)
  simpa only [eval_pow, eval_X, one_pow, Lagrange.interpolate_apply,
    eval_finsetSum, eval_mul, eval_C, ← finiteCoeff_eq_eval_basis, mul_comm] using h.symm

end JanetCartan.Seeley
