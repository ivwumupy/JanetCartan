module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Corank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Nodes

/-!
# Adjugate and corank

The linear algebra used in Proposition `app:ch_seed:prop:seed-strata`.
-/

@[expose] public noncomputable section

namespace JanetCartan

private theorem diagonal_adjugate_eq_zero_iff {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) :
    (Matrix.diagonal d).adjugate = 0 ↔
      2 ≤ (Finset.univ.filter fun i ↦ d i = 0).card := by
  classical
  have he : (Matrix.diagonal d).adjugate = 0 ↔
      ∀ i, ∃ j, j ≠ i ∧ d j = 0 := by
    rw [Matrix.adjugate_diagonal]
    constructor
    · intro h i
      have hi := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i i) h
      simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply] at hi
      simpa using Finset.prod_eq_zero_iff.mp hi
    · intro h
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
        apply Finset.prod_eq_zero_iff.mpr
        simpa using h i
      · simp [Matrix.diagonal_apply_ne _ hij]
  rw [he, show 2 ≤ (Finset.univ.filter fun i ↦ d i = 0).card ↔
    1 < (Finset.univ.filter fun i ↦ d i = 0).card by omega, Finset.one_lt_card]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h ⟨0, hn⟩
    obtain ⟨j, hji, hj⟩ := h i
    exact ⟨i, hi, j, hj, hji.symm⟩
  · rintro ⟨i, hi, j, hj, hij⟩ k
    by_cases hik : i = k
    · exact ⟨j, by simpa [← hik] using hij.symm, hj⟩
    · exact ⟨i, hik, hi⟩

/-- Proposition `app:ch_seed:prop:seed-strata`: for a nonempty real square
matrix, the adjugate vanishes exactly when its corank is at least two. -/
theorem adjugate_eq_zero_iff_rank_add_two_le {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A.adjugate = 0 ↔ A.rank + 2 ≤ n := by
  classical
  obtain ⟨L, R, d, rfl⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  let P := (L.map Matrix.TransvectionStruct.toMatrix).prod
  let Q := (R.map Matrix.TransvectionStruct.toMatrix).prod
  have hp : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hq : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod R
  have hp' : IsUnit P.adjugate := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_adjugate, hp, one_pow]; exact isUnit_one)
  have hq' : IsUnit Q.adjugate := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_adjugate, hq, one_pow]; exact isUnit_one)
  change (P * Matrix.diagonal d * Q).adjugate = 0 ↔ _
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    hq'.mul_right_eq_zero, hp'.mul_left_eq_zero]
  change (Matrix.diagonal d).adjugate = 0 ↔ (P * Matrix.diagonal d * Q).rank + 2 ≤ n
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero Q _ (by rw [hq]; norm_num),
    Matrix.rank_mul_eq_right_of_det_ne_zero P _ (by rw [hp]; norm_num),
    diagonal_adjugate_eq_zero_iff hn, Matrix.rank_diagonal]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i ↦ d i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  rw [Fintype.card_subtype]
  simp only [ne_eq] at *
  omega

/-- Proposition `app:ch_seed:prop:seed-strata`: higher corank makes the
adjugate of the cube pencil zero, and these are all its zero adjugates. -/
theorem cubePencil_adjugate_eq_zero_iff {n : ℕ} (hn : 5 ≤ n) (ξ : Euclidean n) :
    (cubePencil ξ).adjugate = 0 ↔ 2 ≤ Module.finrank ℝ (cubePencilKernel ξ) := by
  rw [adjugate_eq_zero_iff_rank_add_two_le (by omega)]
  have h := cubePencil_rank_add_finrank_kernel ξ
  omega

/-- Proposition `app:ch_seed:prop:seed-strata`: at corank one the symmetric
cube pencil has a nonzero rank-one adjugate along an actual kernel vector. -/
theorem cubePencil_adjugate_factorization_of_corank_one {n : ℕ} (hn : 5 ≤ n)
    (ξ : Euclidean n) (hd : cubeDeterminant ξ = 0)
    (hk : Module.finrank ℝ (cubePencilKernel ξ) = 1) :
    ∃ v : Euclidean n, v ≠ 0 ∧ (fun i ↦ v i) ∈ cubePencilKernel ξ ∧
      ∃ a : ℝ, a ≠ 0 ∧ (cubePencil ξ).adjugate = fun i j ↦ a * v i * v j := by
  classical
  let A := cubePencil ξ
  have hA : A.adjugate ≠ 0 := by
    intro h
    have := (cubePencil_adjugate_eq_zero_iff hn ξ).mp h
    omega
  have hcol (j : Fin n) : (fun i ↦ A.adjugate i j) ∈ cubePencilKernel ξ := by
    change A.mulVec (fun i ↦ A.adjugate i j) = 0
    have hm : A * A.adjugate = 0 := by
      rw [Matrix.mul_adjugate, show A.det = 0 from hd, zero_smul]
    funext i
    exact congrArg (fun B : Matrix (Fin n) (Fin n) ℝ ↦ B i j) hm
  obtain ⟨k, j, hkj⟩ : ∃ k j, A.adjugate k j ≠ 0 := by
    by_contra! h
    exact hA (by ext k j; exact h k j)
  let v : Euclidean n := WithLp.toLp 2 (fun i ↦ A.adjugate i j)
  have hvk : v k ≠ 0 := hkj
  have hv : v ≠ 0 := by intro h; exact hvk (congrArg (fun w : Euclidean n ↦ w k) h)
  have hvker : (fun i ↦ v i) ∈ cubePencilKernel ξ := hcol j
  have hsub : (⟨fun i ↦ v i, hvker⟩ : cubePencilKernel ξ) ≠ 0 := by
    intro h
    exact hvk (congrArg (fun w : cubePencilKernel ξ ↦ w.val k) h)
  have hex (l : Fin n) : ∃ s : ℝ, (fun i ↦ A.adjugate i l) = s • (fun i ↦ v i) := by
    obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_eq_one hk hsub
      (⟨fun i ↦ A.adjugate i l, hcol l⟩ : cubePencilKernel ξ)
    exact ⟨s, (congrArg Subtype.val hs).symm⟩
  choose s hs using hex
  have hentry (i l : Fin n) : A.adjugate i l = s l * v i := congrFun (hs l) i
  have hsymm : A.IsSymm := by
    ext i l
    dsimp [A, cubePencil]
    by_cases hi : i = l
    · subst l; rfl
    · simp [hi, Ne.symm hi]
  have hs' (l : Fin n) : s l = (s k / v k) * v l := by
    have he := hsymm.adjugate.apply l k
    rw [hentry, hentry] at he
    apply (mul_right_cancel₀ hvk)
    calc s l * v k = s k * v l := he
         _ = (s k / v k * v l) * v k := by field_simp
  have hf : A.adjugate = fun i l ↦ (s k / v k) * v i * v l := by
    ext i l
    rw [hentry, hs']
    ring
  refine ⟨v, hv, hvker, s k / v k, ?_, hf⟩
  intro ha
  apply hA
  rw [hf, ha]
  ext i l
  simp

end JanetCartan
