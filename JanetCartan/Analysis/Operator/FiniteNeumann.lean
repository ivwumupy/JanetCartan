module

public import JanetCartan.Analysis.Operator.FiniteNeumann.Algebra
public import JanetCartan.Analysis.Operator.FiniteNeumann.Decay
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Neumann expansion and observed remainder

This proves `app:ch_regular:eq:finite-neumann-identity` and the deduction of
`app:ch_regular:eq:finite-observation` from the exact quantitative estimate
`app:ch_regular:eq:inverse-remainder`. The latter smoothing estimate, including
regularity, remains an explicit input: this module does not prove it from the
negative Sobolev bounds on the source or the coefficient profile.

`K` and `T` are actual continuous linear endomorphisms of one base space.
The existing `GradedScale` represents their higher Sobolev domains, so neither
the inverse nor the domains change with proof depth. The observation is linear
and has a polynomial bound between the indicated levels. Both the smoothing
and observation estimates carry explicit level membership; the extension of
`gradeNorm` by zero outside its domain cannot certify any regularity assertion.

The family theorem chooses one positive finite depth and one constant before
the family index, which may encode frequency, coefficients, and source data.
-/

@[expose] public noncomputable section

namespace JanetCartan

open Finset

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sign in `app:ch_regular:eq:finite-neumann-identity` does not change a
Sobolev norm, with membership in the norm's domain retained. -/
theorem GradedScale.gradeNorm_neg_one_pow_smul (G : GradedScale E) (s d : ℕ)
    {v : E} (hv : v ∈ G.level s) :
    G.gradeNorm s (((-1 : ℝ) ^ d) • v) = G.gradeNorm s v := by
  rw [G.gradeNorm_eq ((G.level s).smul_mem _ hv), G.gradeNorm_eq hv]
  change G.seminorm s (((-1 : ℝ) ^ d) • (⟨v, hv⟩ : G.level s)) = _
  rw [map_smul_eq_mul]
  simp

/-- Quantitative remainder at depth `N + t` in
`app:ch_regular:eq:finite-observation`. The premise `hpower` is precisely
`app:ch_regular:eq:inverse-remainder` at input order `t`; `hpower_mem` supplies
its regularity assertion. The conclusion retains the full polynomial loss. -/
theorem finite_neumann_observation_bound (G : GradedScale E) (H : GradedScale F)
    (K T : E →L[ℝ] E) (hT : T * (1 + K) = 1) (B : E →ₗ[ℝ] F)
    (h : E) (s t N : ℕ) {ρ L σ c A CB CP : ℝ}
    (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (hσ : 0 ≤ σ) (hscale : L ≤ ρ ^ (1 - σ))
    (hA : 0 ≤ A) (hCB : 0 ≤ CB) (hCP : 0 ≤ CP)
    (hB_mem : ∀ v, v ∈ G.level t → B v ∈ H.level s)
    (hB : ∀ v, v ∈ G.level t → H.gradeNorm s (B v) ≤ CB * ρ ^ c * G.gradeNorm t v)
    (hpower_mem : T ((K ^ (N + t)) h) ∈ G.level t)
    (hpower : G.gradeNorm t (T ((K ^ (N + t)) h)) ≤ CP * A * L ^ t * (L / ρ) ^ N) :
    B (T h) - (∑ j ∈ range (N + t), ((-1 : ℝ) ^ j) • B ((K ^ j) h)) ∈ H.level s ∧
    H.gradeNorm s (B (T h) -
        (∑ j ∈ range (N + t), ((-1 : ℝ) ^ j) • B ((K ^ j) h))) ≤
      (CB * CP) * A * ρ ^ (c + (t : ℝ) - σ * N) := by
  rw [finite_neumann_observation_identity K T hT B (N + t) h]
  have hmem := hB_mem _ hpower_mem
  refine ⟨(H.level s).smul_mem _ hmem, ?_⟩
  rw [H.gradeNorm_neg_one_pow_smul s (N + t) hmem]
  calc
    H.gradeNorm s (B (T ((K ^ (N + t)) h)))
        ≤ CB * ρ ^ c * G.gradeNorm t (T ((K ^ (N + t)) h)) := hB _ hpower_mem
    _ ≤ CB * ρ ^ c * (CP * A * L ^ t * (L / ρ) ^ N) := by
      exact mul_le_mul_of_nonneg_left hpower (mul_nonneg hCB (Real.rpow_nonneg (by linarith) _))
    _ = (CB * CP) * A * (ρ ^ c * L ^ t * (L / ρ) ^ N) := by ring
    _ ≤ (CB * CP) * A * ρ ^ (c + (t : ℝ) - σ * N) :=
      mul_le_mul_of_nonneg_left
        (finite_neumann_scale_bound hρ (by linarith) hσ hscale t N)
        (mul_nonneg (mul_nonneg hCB hCP) hA)

/-- Uniform arbitrary accuracy in `app:ch_regular:eq:finite-observation`.
For each fixed output order `s`, input order `t`, and accuracy `Q`, one depth
`d ≥ 1` works for the entire family. The constants `CB` and `CP N` are uniform
in the index. The smoothing estimate `app:ch_regular:eq:inverse-remainder`
and the polynomial observation bounds are inputs, not conclusions of this theorem. -/
theorem exists_finite_neumann_observation_depth {ι : Type*}
    (G : GradedScale E) (H : GradedScale F)
    (K T : ι → E →L[ℝ] E) (B : ι → E →ₗ[ℝ] F) (h : ι → E)
    (ρ L A : ι → ℝ) (s t : ℕ) (σ c Q CB : ℝ) (CP : ℕ → ℝ)
    (hT : ∀ i, T i * (1 + K i) = 1)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hσ : 0 < σ) (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ))
    (hA : ∀ i, 0 ≤ A i) (hCB : 0 ≤ CB) (hCP : ∀ N, 0 ≤ CP N)
    (hB_mem : ∀ i v, v ∈ G.level t → B i v ∈ H.level s)
    (hB : ∀ i v, v ∈ G.level t →
      H.gradeNorm s (B i v) ≤ CB * (ρ i) ^ c * G.gradeNorm t v)
    (hpower_mem : ∀ i N, T i (((K i) ^ (N + t)) (h i)) ∈ G.level t)
    (hpower : ∀ i N, G.gradeNorm t (T i (((K i) ^ (N + t)) (h i))) ≤
      CP N * A i * (L i) ^ t * (L i / ρ i) ^ N) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      B i (T i (h i)) - (∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i)))
        ∈ H.level s ∧
      H.gradeNorm s (B i (T i (h i)) -
          (∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i)))) ≤
        C * A i * (ρ i) ^ (-Q) := by
  obtain ⟨N, hNpos, hN⟩ := exists_finite_neumann_order hσ c Q t
  refine ⟨N + t, (Nat.succ_le_of_lt hNpos).trans (Nat.le_add_right N t),
    CB * CP N, mul_nonneg hCB (hCP N), ?_⟩
  intro i
  obtain ⟨hmem, hbound⟩ := finite_neumann_observation_bound G H (K i) (T i) (hT i)
    (B i) (h i) s t N (hρ i) (hL i) hσ.le (hscale i) (hA i) hCB (hCP N)
    (hB_mem i) (hB i) (hpower_mem i N) (hpower i N)
  refine ⟨hmem, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hρ i) hN)
    (mul_nonneg (mul_nonneg hCB (hCP N)) (hA i))

end JanetCartan
