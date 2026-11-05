module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Partitions

/-!
# Composition budgets for the full normal amplitude

The consumer is `exists_crossNormalAmplitude_oneHigh_bound`, for
`app:ch_regular_base:eq:actual-one-high`. The baseline-one exponent is retained
at every intermediate order, so that the second composition uses the same high
norm without multiplying two high norms.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.FourierIntegral.NormalOneHigh
open CompositionBounds

/-- The finite partition constant in the full normal-amplitude chain rule
(`app:ch_regular_base:lem:buffered-interpolation`). -/
def compositionBudget (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p : OrderedFinpartition k, a p.length * ∏ i, b (p.partSize i)

/-- Positivity of the constant used in the two normal-amplitude compositions. -/
theorem compositionBudget_nonneg {a b : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (k : ℕ) :
    0 ≤ compositionBudget a b k :=
  Finset.sum_nonneg (fun p _ ↦ mul_nonneg (ha p.length)
    (Finset.prod_nonneg (fun i _ ↦ hb (p.partSize i))))

/-- The exact exponent budget, at every positive order through the chosen top
order. Source: `app:ch_regular_base:lem:buffered-interpolation`. -/
theorem partition_exponent_identity {s k : ℕ} (p : OrderedFinpartition k) :
    ((p.length : ℝ) - 1) / (s - 1) +
      ∑ i, ((p.partSize i : ℝ) - 1) / (s - 1) = ((k : ℝ) - 1) / (s - 1) := by
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [← Nat.cast_sum, sum_partSize, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Composition preserves the primitive baseline-one profile. This is used
first for the coefficient operation and then for the supplied inverse chart in
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_iteratedFDeriv_comp_le_profile
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {x : E} {s k : ℕ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (hk : 1 ≤ k) (hks : k ≤ s) {H : ℝ} (hH : 0 < H)
    (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (houter : ∀ i, 1 ≤ i → i ≤ s →
      ‖iteratedFDeriv ℝ i g (f x)‖ ≤ a i * H ^ (((i : ℝ) - 1) / (s - 1)))
    (hinner : ∀ i, 1 ≤ i → i ≤ s →
      ‖iteratedFDeriv ℝ i f x‖ ≤ b i * H ^ (((i : ℝ) - 1) / (s - 1))) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤
      compositionBudget a b k * H ^ (((k : ℝ) - 1) / (s - 1)) := by
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    (hg.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hf.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) (le_refl k)).trans
  unfold compositionBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  have hp : 1 ≤ p.length := p.length_pos hk
  calc
    _ ≤ (a p.length * H ^ (((p.length : ℝ) - 1) / (s - 1))) *
        ∏ i, b (p.partSize i) * H ^ (((p.partSize i : ℝ) - 1) / (s - 1)) := by
      exact mul_le_mul (houter _ hp (p.length_le.trans hks))
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun i _ ↦ hinner _ (p.partSize_pos i) ((p.partSize_le i).trans hks)))
        (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
        (mul_nonneg (ha _) (Real.rpow_nonneg hH.le _))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hH,
        mul_mul_mul_comm, ← Real.rpow_add hH, partition_exponent_identity]

end JanetCartan.FourierIntegral.NormalOneHigh
