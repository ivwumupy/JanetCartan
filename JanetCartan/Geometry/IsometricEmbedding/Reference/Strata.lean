module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Strata.Adjugate

/-!
# The complete bad set of the cube pencil

Proposition `app:ch_seed:prop:seed-strata` of `paper.tex`: the nonzero
multiple characteristic set is exactly the union of the coordinate strata
and the cube node lines.
-/

@[expose] public noncomputable section

namespace JanetCartan

/-- Proposition `app:ch_seed:prop:seed-strata`: a singular cube pencil has
positive corank. -/
theorem cubePencilKernel_finrank_pos_of_det_eq_zero {n : ℕ} {ξ : Euclidean n}
    (hd : cubeDeterminant ξ = 0) : 0 < Module.finrank ℝ (cubePencilKernel ξ) := by
  by_contra h
  have hk : cubePencilKernel ξ = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hi : Function.Injective (cubePencil ξ).mulVec := LinearMap.ker_eq_bot.mp hk
  have hu := Matrix.mulVec_injective_iff_isUnit.mp hi
  have hd' := (Matrix.isUnit_iff_isUnit_det _).mp hu
  exact hd'.ne_zero hd

/-- Proposition `app:ch_seed:prop:seed-strata`: positive corank forces a zero
determinant. -/
theorem cubeDeterminant_eq_zero_of_kernel_finrank_pos {n : ℕ} {ξ : Euclidean n}
    (hk : 0 < Module.finrank ℝ (cubePencilKernel ξ)) : cubeDeterminant ξ = 0 := by
  by_contra hd
  have hr := Matrix.rank_of_det_ne_zero hd
  have he := cubePencil_rank_add_finrank_kernel ξ
  simp only [Fintype.card_fin] at hr
  omega

/-- Proposition `app:ch_seed:prop:seed-strata`: the complete classification,
proved using the adjugate/corank implications and the common quadratic zeros. -/
theorem cubeDeterminant_multiple_iff_strata {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    (cubeDeterminant ξ = 0 ∧ fderiv ℝ cubeDeterminant ξ = 0) ↔
      (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0) ∨
      (∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0) ∨
      (∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, ξ = t • cubeVector a b) := by
  constructor
  · rintro ⟨hd, hg⟩
    by_cases hk : 2 ≤ Module.finrank ℝ (cubePencilKernel ξ)
    · rcases (two_le_finrank_cubePencilKernel_iff hn hξ).mp hk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hpos := cubePencilKernel_finrank_pos_of_det_eq_zero hd
      have hone : Module.finrank ℝ (cubePencilKernel ξ) = 1 := by omega
      obtain ⟨v, hv, hvk, a, ha, hf⟩ :=
        cubePencil_adjugate_factorization_of_corank_one hn ξ hd hone
      have hq := (fderiv_cubeDeterminant_eq_zero_iff_of_adjugate_eq ξ v a ha hf).mp hg
      obtain ⟨i, j, hij, t, ht⟩ := (cubeQuadraticContraction_eq_zero_iff_node hn hv).mp hq
      have hq' (i : Fin n) : v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 = 0 := by
        simpa only [cubeQuadraticContraction_apply, PiLp.zero_apply] using
          congrArg (fun w : Euclidean n ↦ w i) hq
      have hx := cubePencil_covector_eq_smul_of_common_zero hn hv hq' hvk
      refine Or.inr (Or.inr ⟨i, j, hij, ((∑ k, ξ k) / (∑ k, v k)) * t, ?_⟩)
      calc ξ = ((∑ k, ξ k) / (∑ k, v k)) • v := hx
           _ = _ := by rw [ht, smul_smul]
  · intro hs
    have high (hk : 2 ≤ Module.finrank ℝ (cubePencilKernel ξ)) :
        cubeDeterminant ξ = 0 ∧ fderiv ℝ cubeDeterminant ξ = 0 :=
      ⟨cubeDeterminant_eq_zero_of_kernel_finrank_pos (by omega),
        fderiv_cubeDeterminant_eq_zero_of_adjugate_eq_zero ξ
          ((cubePencil_adjugate_eq_zero_iff hn ξ).mpr hk)⟩
    rcases hs with h | h | ⟨a, b, hab, t, rfl⟩
    · exact high ((two_le_finrank_cubePencilKernel_iff hn hξ).mpr (Or.inl h))
    · exact high ((two_le_finrank_cubePencilKernel_iff hn hξ).mpr (Or.inr h))
    · have ht : t ≠ 0 := by intro ht; simp [ht] at hξ
      exact ⟨cubeDeterminant_node_eq_zero hn hab ht,
        fderiv_cubeDeterminant_node_eq_zero hn hab ht⟩

/-- The space `L_{ijk}` in Proposition `app:ch_seed:prop:seed-strata`. -/
def cubeTripleZeroSpace {n : ℕ} (i j k : Fin n) : Submodule ℝ (Euclidean n) where
  carrier := {ξ | ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hi, hj, hk⟩ ⟨hi', hj', hk'⟩; simp_all
  smul_mem' := by rintro a x ⟨hi, hj, hk⟩; simp_all

/-- The space `L_{ijS}` in Proposition `app:ch_seed:prop:seed-strata`. -/
def cubeDoubleZeroSumSpace {n : ℕ} (i j : Fin n) : Submodule ℝ (Euclidean n) where
  carrier := {ξ | ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hi, hj, hs⟩ ⟨hi', hj', hs'⟩
    simp_all [PiLp.add_apply, Finset.sum_add_distrib]
  smul_mem' := by
    rintro a x ⟨hi, hj, hs⟩
    simp_all [PiLp.smul_apply, ← Finset.mul_sum]

/-- The node line `ℝ ℓ_{ab}` in Proposition `app:ch_seed:prop:seed-strata`. -/
def cubeNodeLine {n : ℕ} (a b : Fin n) : Submodule ℝ (Euclidean n) :=
  Submodule.span ℝ {cubeVector a b}

/-- The finite family `𝓛` of bad subspaces in Proposition
`app:ch_seed:prop:seed-strata`, with distinct coordinate indices. -/
def cubeBadSubspaces (n : ℕ) : Finset (Submodule ℝ (Euclidean n)) := by
  classical
  exact
    ((Finset.univ.filter fun p : Fin n × Fin n × Fin n ↦
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2).image
        fun p ↦ cubeTripleZeroSpace p.1 p.2.1 p.2.2) ∪
    ((Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 ≠ p.2).image
        fun p ↦ cubeDoubleZeroSumSpace p.1 p.2) ∪
    ((Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 ≠ p.2).image
        fun p ↦ cubeNodeLine p.1 p.2)

/-- The union of the finite bad-subspace family in Proposition
`app:ch_seed:prop:seed-strata`, including the origin. -/
def cubeBadSubspaceUnion (n : ℕ) : Set (Euclidean n) :=
  ⋃ L ∈ cubeBadSubspaces n, (L : Set (Euclidean n))

/-- Proposition `app:ch_seed:prop:seed-strata`: membership in the finite
subspace union is exactly the three displayed types of strata. -/
theorem mem_cubeBadSubspaceUnion_iff {n : ℕ} (ξ : Euclidean n) :
    ξ ∈ cubeBadSubspaceUnion n ↔
      (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ξ i = 0 ∧ ξ j = 0 ∧ ξ k = 0) ∨
      (∃ i j : Fin n, i ≠ j ∧ ξ i = 0 ∧ ξ j = 0 ∧ ∑ k, ξ k = 0) ∨
      (∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, ξ = t • cubeVector a b) := by
  classical
  simp only [cubeBadSubspaceUnion, Set.mem_iUnion, SetLike.mem_coe,
    cubeBadSubspaces, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨L, (⟨i, j, k, hijk, rfl⟩ | ⟨i, j, hij, rfl⟩) | ⟨a, b, hab, rfl⟩, hx⟩
    · exact Or.inl ⟨i, j, k, hijk.1, hijk.2.1, hijk.2.2, hx⟩
    · exact Or.inr (Or.inl ⟨i, j, hij, hx⟩)
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
      exact Or.inr (Or.inr ⟨a, b, hab, t, ht.symm⟩)
  · rintro (⟨i, j, k, hij, hik, hjk, hx⟩ | ⟨i, j, hij, hx⟩ | ⟨a, b, hab, t, ht⟩)
    · exact ⟨_, Or.inl (Or.inl ⟨i, j, k, ⟨hij, hik, hjk⟩, rfl⟩), hx⟩
    · exact ⟨_, Or.inl (Or.inr ⟨i, j, hij, rfl⟩), hx⟩
    · exact ⟨_, Or.inr ⟨a, b, hab, rfl⟩, Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩⟩

/-- Proposition `app:ch_seed:prop:seed-strata`: the nonzero bad set is the
finite subspace union with its origin removed. -/
theorem cubeDeterminant_multiple_set_eq (n : ℕ) (hn : 5 ≤ n) :
    {ξ : Euclidean n | cubeDeterminant ξ = 0 ∧ fderiv ℝ cubeDeterminant ξ = 0 ∧ ξ ≠ 0} =
      cubeBadSubspaceUnion n \ {0} := by
  ext ξ
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · rw [mem_cubeBadSubspaceUnion_iff, ← cubeDeterminant_multiple_iff_strata hn hξ]
    tauto

/-- Proposition `app:ch_seed:prop:seed-strata`: the origin belongs to the
bad-subspace union in the source dimension. -/
theorem zero_mem_cubeBadSubspaceUnion {n : ℕ} (hn : 5 ≤ n) :
    (0 : Euclidean n) ∈ cubeBadSubspaceUnion n := by
  rw [mem_cubeBadSubspaceUnion_iff]
  exact Or.inr (Or.inr ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
    by intro h; exact Nat.zero_ne_one (congrArg Fin.val h), 0, by simp⟩)

/-- Proposition `app:ch_seed:prop:seed-strata`: outside the finite bad
subspace union the pencil has rank at least `n - 1`. -/
theorem cubePencil_rank_ge_of_not_mem_badSubspaceUnion {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ∉ cubeBadSubspaceUnion n) :
    n - 1 ≤ (cubePencil ξ).rank := by
  have hne : ξ ≠ 0 := by rintro rfl; exact hξ (zero_mem_cubeBadSubspaceUnion hn)
  have hk : ¬ 2 ≤ Module.finrank ℝ (cubePencilKernel ξ) := by
    intro hk
    apply hξ
    rw [mem_cubeBadSubspaceUnion_iff]
    rcases (two_le_finrank_cubePencilKernel_iff hn hne).mp hk with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hr := cubePencil_rank_add_finrank_kernel ξ
  omega

/-- Proposition `app:ch_seed:prop:seed-strata`: every determinant zero
outside the finite bad-subspace union is a simple characteristic. -/
theorem fderiv_cubeDeterminant_ne_zero_of_not_mem_badSubspaceUnion {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ∉ cubeBadSubspaceUnion n) (hd : cubeDeterminant ξ = 0) :
    fderiv ℝ cubeDeterminant ξ ≠ 0 := by
  have hne : ξ ≠ 0 := by rintro rfl; exact hξ (zero_mem_cubeBadSubspaceUnion hn)
  intro hg
  exact hξ ((mem_cubeBadSubspaceUnion_iff ξ).mpr
    ((cubeDeterminant_multiple_iff_strata hn hne).mp ⟨hd, hg⟩))

end JanetCartan
