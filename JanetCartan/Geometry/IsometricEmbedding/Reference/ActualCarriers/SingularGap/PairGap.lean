module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.MinorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Strata.Adjugate

/-!
# A uniform bound on two orthonormal directions

For `app:ch_seed:prop:seed-actual-menu`, item 1 and Step 2, a bounded
family of real matrices with a positive Frobenius adjugate gap cannot
annihilate two orthonormal vectors. Compactness makes the sum of their
image norms uniformly positive. `SingularGap` applies this to the last
two right singular vectors to obtain the numbered singular-value bound.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

/-- The literal column-vector action in the original real coordinates of
`app:ch_seed:prop:seed-actual-menu`, item 1. No transpose or coordinate
permutation enters the Euclidean map used for singular values. -/
theorem toEuclideanLin_apply_coordinate {n : ℕ} (A : MetricTensor n) (v : Euclidean n) (i : Fin n) :
    A.toEuclideanLin v i = ∑ j, A i j * v j := rfl

private theorem continuous_matrix_euclidean_apply {n : ℕ} :
    Continuous (fun p : MetricTensor n × Euclidean n ↦ p.1.toEuclideanLin p.2) := by
  change Continuous (fun p : MetricTensor n × Euclidean n ↦
    WithLp.toLp 2 (fun i ↦ ∑ j, p.1 i j * p.2 j))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ (fun j _ ↦
    (((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd)))

private theorem orthonormal_pair_image_sum_pos {n : ℕ} (hn : 0 < n) (A : MetricTensor n)
    (hA : A.adjugate ≠ 0) (b : Fin 2 → Euclidean n) (hb : Orthonormal ℝ b) :
    0 < ∑ i, ‖A.toEuclideanLin (b i)‖ := by
  by_contra! h
  have hz : ∑ i, ‖A.toEuclideanLin (b i)‖ = 0 :=
    le_antisymm h (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hker (i) : A.toEuclideanLin (b i) = 0 := by
    exact norm_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ norm_nonneg (A.toEuclideanLin (b i)))).mp hz i (Finset.mem_univ i))
  let b' : Fin 2 → A.toEuclideanLin.ker := fun i ↦ ⟨b i, hker i⟩
  have hb' : Orthonormal ℝ b' := by
    rw [orthonormal_iff_ite] at hb ⊢
    exact hb
  have hdim : 2 ≤ Module.finrank ℝ A.toEuclideanLin.ker := by
    simpa using hb'.linearIndependent.fintype_card_le_finrank
  have hrank : A.rank = Module.finrank ℝ A.toEuclideanLin.range :=
    A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hnull := A.toEuclideanLin.finrank_range_add_finrank_ker
  rw [finrank_euclideanSpace_fin, ← hrank] at hnull
  exact hA ((adjugate_eq_zero_iff_rank_add_two_le hn A).mpr (by omega))

private theorem isCompact_orthonormal_pairs {n : ℕ} :
    IsCompact {b : Fin 2 → Euclidean n | Orthonormal ℝ b} := by
  have hc : IsClosed {b : Fin 2 → Euclidean n | Orthonormal ℝ b} := by
    simp_rw [orthonormal_iff_ite, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  apply (isCompact_closedBall (0 : Fin 2 → Euclidean n) 1).of_isClosed_subset hc
  intro b hb
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
      (fun i ↦ (hb.norm_eq_one i).le)

/-- Uniformly over matrices of bounded Frobenius norm with a positive
adjugate gap, the sum of the image norms of any two orthonormal vectors
has a positive lower bound. The constants precede the matrix and the
vectors. This is the compactness input for the numbered singular-value
estimate in `app:ch_seed:prop:seed-actual-menu`, item 1 and Step 2. -/
theorem exists_uniform_orthonormal_pair_image_gap {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : MetricTensor n,
      a ≤ ‖A.adjugate‖ → ‖A‖ ≤ M →
      ∀ b : Fin 2 → Euclidean n, Orthonormal ℝ b →
        c ≤ ∑ i, ‖A.toEuclideanLin (b i)‖ := by
  have hK : IsCompact {A : MetricTensor n | ‖A‖ ≤ M ∧ a ≤ ‖A.adjugate‖} := by
    have hclosed : IsClosed {A : MetricTensor n | ‖A‖ ≤ M ∧ a ≤ ‖A.adjugate‖} :=
      (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const continuous_id.matrix_adjugate.norm)
    apply (isCompact_closedBall (0 : MetricTensor n) M).of_isClosed_subset hclosed
    intro A hA
    simpa only [Metric.mem_closedBall, dist_zero_right] using hA.1
  have hc : Continuous (fun p : MetricTensor n × (Fin 2 → Euclidean n) ↦
      ∑ i, ‖p.1.toEuclideanLin (p.2 i)‖) := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_matrix_euclidean_apply.comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).norm
  obtain ⟨c, hcpos, hbound⟩ :=
    (hK.prod isCompact_orthonormal_pairs).exists_forall_le' hc.continuousOn
      (fun p hp ↦ orthonormal_pair_image_sum_pos hn p.1
        (norm_pos_iff.mp (ha.trans_le hp.1.2)) p.2 hp.2)
  exact ⟨c, hcpos, fun A hgap hM b hb ↦ hbound (A, b) ⟨⟨hM, hgap⟩, hb⟩⟩

end JanetCartan.ActualCarriers
