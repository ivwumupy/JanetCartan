module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Partitions

/-!
# Reserve arithmetic for a varying critical graph

Both maps in the moving-segment composition vary with the phase. The
partition estimate here preserves a positive common reserve, unlike a
bound treating all inner jets as scale independent. The consumer is the
critical-map and segment induction for `new:eq:carrier-coefficient` and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

/-- The outer and inner derivative excesses in a chain-rule partition spend
one common positive reserve (`new:eq:carrier-coefficient`). -/
theorem partition_comp_reserve_le {k R : ℕ} (p : OrderedFinpartition k) (hR : 1 ≤ R) :
    (p.length - R) + ∑ i, (p.partSize i - R) ≤ k - R := by
  by_cases hp : p.length ≤ R
  · simpa [Nat.sub_eq_zero_of_le hp] using GradedPrimitives.partition_sub_reserve_le p R
  · have hsum : ∑ i, (p.partSize i - R) ≤ ∑ i, (p.partSize i - 1) :=
      Finset.sum_le_sum fun i _ ↦ Nat.sub_le_sub_left hR _
    have he := FlowForcing.sum_partSize_sub_one_add_length p
    omega

/-- Composition of two varying reserve-graded maps preserves a positive
reserve. Constants depend only on the primitive profiles and order; the
scale and maps are chosen afterwards (`new:eq:carrier-coefficient`). -/
theorem norm_jet_comp_reserve_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {g : Y → Z} {x : X} {N k R : ℕ}
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x)) (hk : k ≤ N)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hgjet : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A j * L ^ (j - R))
    (hfjet : ∀ j, 1 ≤ j → j ≤ k →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B j * L ^ (j - R)) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤
      GradedPrimitives.compositionConstant A B k * L ^ (k - R) := by
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum hg hf hk).trans
  rw [GradedPrimitives.compositionConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  calc
    _ ≤ (A p.length * L ^ (p.length - R)) *
        ∏ i, (B (p.partSize i) * L ^ (p.partSize i - R)) :=
      mul_le_mul (hgjet _ p.length_le)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          (fun i _ ↦ hfjet _ (p.partSize_pos i) (p.partSize_le i)))
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (mul_nonneg (hA _) (pow_nonneg (zero_le_one.trans hL) _))
    _ = (A p.length * ∏ i, B (p.partSize i)) *
        L ^ ((p.length - R) + ∑ i, (p.partSize i - R)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (partition_comp_reserve_le p hR))
      (mul_nonneg (hA _) (Finset.prod_nonneg fun _ _ ↦ hB _))

end JanetCartan.ResponseTransfer.DirectEvolution
