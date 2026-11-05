module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Algebra
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Paired reciprocal carriers

The explicit construction following `app:ch_seed:eq:seed-pair-criterion` in
Proposition `app:ch_seed:prop:seed-frozen-menu`, Step 1.
-/

@[expose] public noncomputable section

namespace JanetCartan.CubeCarrier

/-- A nonzero affine polynomial is nonzero at arbitrarily small positive parameters;
used in `app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem exists_small_nonzero_affine {u v ε : ℝ} (hε : 0 < ε) (h : u ≠ 0 ∨ v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ u + t * v ≠ 0 := by
  by_cases hhalf : u + (ε / 2) * v = 0
  · refine ⟨ε / 3, by linarith, by linarith, ?_⟩
    intro hthird
    have hv : v = 0 := by
      have : ε * v = 0 := by nlinarith [hhalf, hthird]
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hε)
    rcases h with hu | hv' <;> simp_all
  · exact ⟨ε / 2, by linarith, by linarith, hhalf⟩

/-- The cube normalization for `n ≥ 5` in `app:ch_seed:defn:seed-cube`. -/
theorem coefficient_mul_dimension_sq {n : ℕ} (hn : 5 ≤ n) : cubeCoefficient n * ((n : ℝ) - 4)^2 = 1 := by
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact inv_mul_cancel₀ (pow_ne_zero 2 hd)

/-- The signed two-pair vector in `app:ch_seed:prop:seed-frozen-menu`, Step 1.
The embedding records four distinct coordinate positions. -/
def paired {n : ℕ} (p : Fin 4 ↪ Fin n) (x y : ℝ) : Euclidean n :=
  WithLp.toLp 2 fun i ↦
    if i = p 0 then -x else if i = p 1 then x else
    if i = p 2 then -y else if i = p 3 then y else 1

/-- Expansion of the two-pair vector into coordinate indicators
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem paired_apply_eq_sum {n : ℕ} (p : Fin 4 ↪ Fin n) (x y : ℝ) (i : Fin n) :
    paired p x y i = 1 + (if i = p 0 then -x-1 else 0) +
      (if i = p 1 then x-1 else 0) + (if i = p 2 then -y-1 else 0) +
      (if i = p 3 then y-1 else 0) := by
  by_cases h0 : i = p 0
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h1 : i = p 1
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h2 : i = p 2
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h3 : i = p 3
  · subst i; simp [paired, p.injective.eq_iff]
  simp [paired, h0, h1, h2, h3]


/-- The two signed pairs cancel, leaving `n-4`
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem sum_paired {n : ℕ} (p : Fin 4 ↪ Fin n) (x y : ℝ) :
    (∑ i, paired p x y i) = (n : ℝ) - 4 := by
  simp_rw [paired_apply_eq_sum]
  simp only [Finset.sum_add_distrib]
  simp
  ring

/-- Coordinate inversion preserves the paired form
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem reciprocal_paired {n : ℕ} (p : Fin 4 ↪ Fin n) (x y : ℝ) :
    reciprocal (paired p x y) = paired p x⁻¹ y⁻¹ := by
  ext i
  simp only [reciprocal_apply, paired]
  split_ifs <;> simp

/-- Nonvanishing of paired coordinates in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem paired_apply_ne_zero {n : ℕ} (p : Fin 4 ↪ Fin n) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (i : Fin n) : paired p x y i ≠ 0 := by
  simp only [paired]
  split_ifs <;> simp_all

/-- The quadratic stress vector is supported on the two pairs
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem quadratic_paired_apply {n : ℕ} (hn : 5 ≤ n) (p : Fin 4 ↪ Fin n) (x y : ℝ)
    (i : Fin n) :
    quadratic (paired p x y) i =
      (if i = p 0 then x^2-1 else 0) + (if i = p 1 then x^2-1 else 0) +
      (if i = p 2 then y^2-1 else 0) + (if i = p 3 then y^2-1 else 0) := by
  change paired p x y i ^ 2 - cubeCoefficient n * (∑ j, paired p x y j)^2 = _
  rw [sum_paired, coefficient_mul_dimension_sq hn]
  by_cases h0 : i = p 0
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h1 : i = p 1
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h2 : i = p 2
  · subst i; simp [paired, p.injective.eq_iff]
  by_cases h3 : i = p 3
  · subst i; simp [paired, p.injective.eq_iff]
  simp [paired, h0, h1, h2, h3]

/-- Pairing with the quadratic vector depends only on the pair sums
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem paired_quadratic_pairing {n : ℕ} (hn : 5 ≤ n) (p : Fin 4 ↪ Fin n) (x y : ℝ)
    (s : Euclidean n) :
    (∑ i, s i * quadratic (paired p x y) i) =
      (s (p 0) + s (p 1)) * (x^2-1) + (s (p 2) + s (p 3)) * (y^2-1) := by
  simp_rw [quadratic_paired_apply hn, mul_add, mul_ite, mul_zero]
  simp only [Finset.sum_add_distrib]
  simp
  ring

/-- Arbitrarily small positive parameters preserving the square roots and detection
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem exists_small_detection_parameter {α β S T ε : ℝ} (hε : 0 < ε)
    (hab : α * β * (α - β) ≠ 0) (hST : S ≠ 0 ∨ T ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ 0 < 1 + t * α ∧ 0 < 1 + t * β ∧
      α * S + β * T + t * α * β * (S + T) ≠ 0 := by
  have hD : 0 < |α| + |β| + 1 := by positivity
  have hδ : 0 < min ε (1 / (|α| + |β| + 1)) := lt_min hε (div_pos zero_lt_one hD)
  obtain ⟨t, ht, hbound, hnonzero⟩ := exists_small_nonzero_affine hδ
    (detection_coefficients_not_both_zero hab hST)
  have hsize : t * (|α| + |β| + 1) < 1 :=
    (lt_div_iff₀ hD).mp (lt_of_lt_of_le hbound (min_le_right _ _))
  refine ⟨t, ht, lt_of_lt_of_le hbound (min_le_left _ _), ?_, ?_, ?_⟩
  · nlinarith [neg_abs_le α, abs_nonneg β]
  · nlinarith [neg_abs_le β, abs_nonneg α]
  · convert hnonzero using 1
    ring


/-- The exact rational detecting-pairing formula in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem paired_sqrt_reciprocal_pairing {n : ℕ} (hn : 5 ≤ n) (p : Fin 4 ↪ Fin n) (α β t : ℝ)
    (hA : 0 < 1 + t * α) (hB : 0 < 1 + t * β) (s : Euclidean n) :
    (∑ i, s i * quadratic (reciprocal (paired p (Real.sqrt (1+t*α))
      (Real.sqrt (1+t*β)))) i) =
    -(t * (α * (s (p 0) + s (p 1)) + β * (s (p 2) + s (p 3)) +
      t * α * β * (s (p 0) + s (p 1) + (s (p 2) + s (p 3))))) /
      ((1+t*α)*(1+t*β)) := by
  rw [reciprocal_paired, paired_quadratic_pairing hn]
  simp only [inv_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
  field_simp
  ring

end JanetCartan.CubeCarrier
