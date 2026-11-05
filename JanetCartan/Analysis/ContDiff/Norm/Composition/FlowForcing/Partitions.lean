module

public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# The baseline-one partition budget

The combinatorial and scalar steps in
`app:ch_regular_base:lem:buffered-interpolation` of paper.tex. The analytic
power bounds are explicit inputs to the scalar lemma in this module.
-/

@[expose] public noncomputable section

namespace JanetCartan.FlowForcing

open CompositionBounds

/-- `app:ch_regular_base:lem:buffered-interpolation`: subtracting one from
every part removes exactly the number of parts from the total order. -/
theorem sum_partSize_sub_one_add_length {n : ℕ} (p : OrderedFinpartition n) :
    (∑ i, (p.partSize i - 1)) + p.length = n := by
  calc
    _ = ∑ i, ((p.partSize i - 1) + 1) := by simp [Finset.sum_add_distrib]
    _ = ∑ i, p.partSize i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (p.partSize_pos i)
    _ = n := sum_partSize p

/-- `app:ch_regular_base:lem:buffered-interpolation`: the exact excess identity
`(q - 1) + ∑ (αᵢ - 1) = n - 1` for a nonempty partition. -/
theorem partition_excess_identity {n : ℕ} (p : OrderedFinpartition n)
    (hp : 1 ≤ p.length) :
    (p.length - 1) + ∑ i, (p.partSize i - 1) = n - 1 := by
  have := sum_partSize_sub_one_add_length p
  omega

/-- `app:ch_regular_base:lem:buffered-interpolation`: every inner derivative
in a partition with at least two blocks has strictly lower order. -/
theorem partSize_lt_of_two_le_length {n : ℕ} (p : OrderedFinpartition n)
    (hp : 2 ≤ p.length) (i : Fin p.length) : p.partSize i < n := by
  have hs := sum_partSize_sub_one_add_length p
  have hi : p.partSize i - 1 ≤ ∑ j, (p.partSize j - 1) :=
    Finset.single_le_sum (f := fun j ↦ p.partSize j - 1)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hpos := p.partSize_pos i
  omega

/-- `app:ch_regular_base:lem:buffered-interpolation`: the normalized
baseline-one exponents in each nonlinear chain-rule term add to one. -/
theorem partition_exponent_sum {n : ℕ} (hn : 2 ≤ n) (p : OrderedFinpartition n) :
    ((p.length : ℝ) - 1) / (n - 1) +
      ∑ i, ((p.partSize i : ℝ) - 1) / (n - 1) = 1 := by
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [← Nat.cast_sum, sum_partSize, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- `app:ch_regular_base:lem:buffered-interpolation`: multiplying the actual
baseline-one power profiles produces exactly one power of the high norm. -/
theorem partition_power_product {n : ℕ} (hn : 2 ≤ n) (p : OrderedFinpartition n)
    {H : ℝ} (hH : 0 < H) (K : ℝ) (B : ℕ → ℝ) :
    (K * H ^ (((p.length : ℝ) - 1) / (n - 1))) *
      (∏ i, B (p.partSize i) * H ^ (((p.partSize i : ℝ) - 1) / (n - 1))) =
        (K * ∏ i, B (p.partSize i)) * H := by
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hH]
  rw [mul_mul_mul_comm, ← Real.rpow_add hH, partition_exponent_sum hn p,
    Real.rpow_one]

/-- `app:ch_regular_base:lem:buffered-interpolation`: summing the scalar
Faà di Bruno forcing terms uses only strictly lower inner jets. Analytic power
profiles are assumptions here and must be derived before using this lemma. -/
theorem forcing_sum_le_of_power_profiles {n : ℕ} (hn : 2 ≤ n)
    (a b B : ℕ → ℝ) {K H : ℝ} (hH : 0 < H) (hK : 0 ≤ K)
    (hb : ∀ j, 0 ≤ b j)
    (houter : ∀ q, 2 ≤ q → q ≤ n → a q ≤ K * H ^ (((q : ℝ) - 1) / (n - 1)))
    (hinner : ∀ j, 1 ≤ j → j < n → b j ≤ B j * H ^ (((j : ℝ) - 1) / (n - 1))) :
    (∑ p : OrderedFinpartition n with 2 ≤ p.length,
      a p.length * ∏ i, b (p.partSize i)) ≤
      (∑ p : OrderedFinpartition n with 2 ≤ p.length,
        K * ∏ i, B (p.partSize i)) * H := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hp' : 2 ≤ p.length := (Finset.mem_filter.mp hp).2
  rw [← partition_power_product hn p hH K B]
  apply mul_le_mul (houter _ hp' p.length_le) ?_
    (Finset.prod_nonneg (fun i _ ↦ hb _)) (mul_nonneg hK (Real.rpow_nonneg hH.le _))
  exact Finset.prod_le_prod₀ (fun i _ ↦ hb _) (fun i _ ↦
    hinner _ (p.partSize_pos i) (partSize_lt_of_two_le_length p hp' i))

end JanetCartan.FlowForcing
