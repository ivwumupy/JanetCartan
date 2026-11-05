module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.DeterminantDeriv

import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Common quadratic zeros and cube node lines

The sign-counting argument in Proposition `app:ch_seed:prop:seed-strata` of
`paper.tex`. We classify the common quadratic zeros, identify the kernel and
adjugate on each nonzero node line, and prove that these nodes have corank one
and vanishing determinant differential.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan

private theorem node_vector_sum {n : ℕ} (a b : Fin n) :
    ∑ i, cubeVector a b i = (n : ℝ) - 4 := by
  simp [cubeVector, Finset.sum_sub_distrib]
  ring

private theorem node_vector_sq {n : ℕ} {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    cubeVector a b i ^ 2 = 1 := by
  by_cases ha : i = a
  · subst i
    norm_num [cubeVector, hab]
  · by_cases hb : i = b
    · subst i
      norm_num [cubeVector, ha]
    · simp [cubeVector, ha, hb]

/-- Proposition `app:ch_seed:prop:seed-strata`: a nonzero common quadratic
zero has nonzero coordinate sum. -/
theorem sum_ne_zero_of_cube_quadratic_zero {n : ℕ} {v : Euclidean n}
    (hv : v ≠ 0)
    (hq : ∀ i, v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 = 0) :
    ∑ i, v i ≠ 0 := by
  intro hs
  apply hv
  ext i
  have hi := hq i
  simp only [hs, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at hi
  have : v i = 0 := by nlinarith [sq_nonneg (v i)]
  simpa using this

/-- Proposition `app:ch_seed:prop:seed-strata`: after normalizing a common
quadratic zero by its coordinate sum divided by `n - 4`, exactly two
coordinates have negative sign. -/
theorem cube_quadratic_zero_negative_card {n : ℕ} (hn : 5 ≤ n)
    {v : Euclidean n} (hv : v ≠ 0)
    (hq : ∀ i, v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 = 0) :
    (Finset.univ.filter (fun i ↦ v i = -((∑ j, v j) / ((n : ℝ) - 4)))).card = 2 := by
  classical
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let t : ℝ := (∑ j, v j) / ((n : ℝ) - 4)
  have ht : t ≠ 0 := div_ne_zero (sum_ne_zero_of_cube_quadratic_zero hv hq) hd
  have hsq (i : Fin n) : v i ^ 2 = t ^ 2 := by
    have hi := hq i
    dsimp [t]
    rw [div_pow, div_eq_mul_inv]
    dsimp [cubeCoefficient] at hi
    nlinarith
  have hsign (i : Fin n) : v i = t ∨ v i = -t := (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq i)
  have hcoord (i : Fin n) : v i = t - (if v i = -t then 2 * t else 0) := by
    rcases hsign i with hi | hi
    · rw [hi, ite_eq_right (by intro h; apply ht; linarith)]
      ring
    · rw [ite_eq_left hi, hi]
      ring
  have hsum : ∑ i, v i = (n : ℝ) * t -
      ((Finset.univ.filter (fun i ↦ v i = -t)).card : ℝ) * (2 * t) := by
    conv_lhs => arg 2; ext i; rw [hcoord i]
    rw [Finset.sum_sub_distrib]
    simp [← Finset.sum_filter]
  have hsum' : ∑ i, v i = ((n : ℝ) - 4) * t := by
    dsimp [t]
    field_simp
  have hc : ((Finset.univ.filter (fun i ↦ v i = -t)).card : ℝ) = 2 := by
    apply (mul_right_cancel₀ ht)
    nlinarith [hsum, hsum']
  change (Finset.univ.filter (fun i ↦ v i = -t)).card = 2
  exact_mod_cast hc

/-- Proposition `app:ch_seed:prop:seed-strata`: the quadratic contraction
vanishes along every cube node line, including at the origin. -/
theorem cubeQuadraticContraction_smul_cubeVector {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) (t : ℝ) :
    cubeQuadraticContraction (t • cubeVector a b) = 0 := by
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  ext i
  rw [cubeQuadraticContraction_apply]
  have hs : ∑ j, (t • cubeVector a b) j = t * ((n : ℝ) - 4) := by
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, node_vector_sum]
  rw [hs]
  change (t * cubeVector a b i) ^ 2 - _ = 0
  rw [mul_pow, node_vector_sq hab]
  dsimp [cubeCoefficient]
  field_simp
  ring

/-- Proposition `app:ch_seed:prop:seed-strata`: the nonzero common zeros of
`q₀` are exactly the nonzero points on the cube node lines. -/
theorem cube_quadratic_zero_iff_node {n : ℕ} (hn : 5 ≤ n)
    {v : Euclidean n} (hv : v ≠ 0) :
    (∀ i, v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 = 0) ↔
      ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, v = t • cubeVector a b := by
  classical
  constructor
  · intro hq
    let t : ℝ := (∑ j, v j) / ((n : ℝ) - 4)
    obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp
      (cube_quadratic_zero_negative_card hn hv hq)
    have hmem (i : Fin n) : v i = -t ↔ i = a ∨ i = b := by
      have := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) hpair
      simpa [t] using this
    refine ⟨a, b, hab, t, ?_⟩
    ext i
    change v i = t * cubeVector a b i
    have hi : v i = t ∨ v i = -t := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      have hi := hq i
      dsimp [t]
      rw [div_pow, div_eq_mul_inv]
      dsimp [cubeCoefficient] at hi
      nlinarith
    by_cases ha : i = a
    · rw [(hmem i).mpr (Or.inl ha)]
      subst i
      norm_num [cubeVector, hab]
    · by_cases hb : i = b
      · rw [(hmem i).mpr (Or.inr hb)]
        subst i
        norm_num [cubeVector, ha]
      · have hneg : v i ≠ -t := by simpa [ha, hb] using (hmem i).mp
        have hpos := hi.resolve_right hneg
        simp [cubeVector, ha, hb, hpos]
  · rintro ⟨a, b, hab, t, rfl⟩ i
    simpa only [cubeQuadraticContraction_apply, PiLp.zero_apply] using
      congrArg (fun v : Euclidean n ↦ v i)
        (cubeQuadraticContraction_smul_cubeVector hn hab t)

/-- Proposition `app:ch_seed:prop:seed-strata`: vector-valued form of the
classification of nonzero common quadratic zeros. -/
theorem cubeQuadraticContraction_eq_zero_iff_node {n : ℕ} (hn : 5 ≤ n)
    {v : Euclidean n} (hv : v ≠ 0) :
    cubeQuadraticContraction v = 0 ↔
      ∃ a b : Fin n, a ≠ b ∧ ∃ t : ℝ, v = t • cubeVector a b := by
  rw [← cube_quadratic_zero_iff_node hn hv]
  constructor
  · intro h i
    simpa only [cubeQuadraticContraction_apply, PiLp.zero_apply] using
      congrArg (fun v : Euclidean n ↦ v i) h
  · intro h
    ext i
    simpa only [cubeQuadraticContraction_apply, PiLp.zero_apply] using h i

private theorem node_mulVec_apply {n : ℕ} (ξ : Euclidean n) (w : Fin n → ℝ)
    (i : Fin n) :
    ((cubePencil ξ).mulVec w) i =
      ξ i * w i - cubeCoefficient n * (∑ j, ξ j) * ∑ j, w j := by
  classical
  simp [cubePencil, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ite_mul]

/-- Proposition `app:ch_seed:prop:seed-strata`: the kernel at a nonzero node
is exactly the line generated by its cube vector. -/
theorem cubePencil_node_mulVec_eq_zero_iff {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) (w : Fin n → ℝ) :
    (cubePencil (t • cubeVector a b)).mulVec w = 0 ↔
      ∃ s : ℝ, w = s • (fun i ↦ cubeVector a b i) := by
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs : ∑ j, (t • cubeVector a b) j = t * ((n : ℝ) - 4) := by
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, node_vector_sum]
  have hc : cubeCoefficient n * (t * ((n : ℝ) - 4)) = t / ((n : ℝ) - 4) := by
    dsimp [cubeCoefficient]
    field_simp
  constructor
  · intro hw
    refine ⟨(∑ j, w j) / ((n : ℝ) - 4), ?_⟩
    funext i
    have hi := congrFun hw i
    rw [node_mulVec_apply, hs, hc] at hi
    change (t * cubeVector a b i) * w i - t / ((n : ℝ) - 4) * ∑ j, w j = 0 at hi
    have heq : cubeVector a b i * w i = (∑ j, w j) / ((n : ℝ) - 4) := by
      apply mul_left_cancel₀ ht
      linear_combination hi
    change w i = ((∑ j, w j) / ((n : ℝ) - 4)) * cubeVector a b i
    have hsq := node_vector_sq hab i
    linear_combination cubeVector a b i * heq - w i * hsq
  · rintro ⟨s, rfl⟩
    funext i
    rw [node_mulVec_apply, hs, hc]
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      node_vector_sum, Pi.zero_apply]
    have hsq := node_vector_sq hab i
    field_simp
    rw [hsq]
    ring

/-- Proposition `app:ch_seed:prop:seed-strata`: the matrix kernel at a nonzero
node is the one-dimensional span of its cube vector. -/
theorem cubePencil_node_ker {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) :
    LinearMap.ker (cubePencil (t • cubeVector a b)).mulVecLin =
      Submodule.span ℝ {fun i ↦ cubeVector a b i} := by
  ext w
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
  rw [cubePencil_node_mulVec_eq_zero_iff hn hab ht]
  exact exists_congr (fun _ ↦ eq_comm)

/-- Proposition `app:ch_seed:prop:seed-strata`: every nonzero node has corank one. -/
theorem cubePencil_node_corank {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (cubePencil (t • cubeVector a b)).mulVecLin) = 1 := by
  rw [cubePencil_node_ker hn hab ht]
  apply finrank_span_singleton
  intro h
  have hsq := node_vector_sq hab a
  have ha := congrFun h a
  simp only [Pi.zero_apply] at ha
  rw [ha] at hsq
  norm_num at hsq

/-- Proposition `app:ch_seed:prop:seed-strata`: the determinant vanishes on
nonzero node lines. -/
theorem cubeDeterminant_node_eq_zero {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) :
    cubeDeterminant (t • cubeVector a b) = 0 := by
  have hk := (cubePencil_node_mulVec_eq_zero_iff hn hab ht
    (fun i ↦ cubeVector a b i)).mpr ⟨1, by simp⟩
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hk (i := a)
  rw [mem_nonZeroDivisors_iff_ne_zero]
  norm_num [cubeVector, hab]

/-- Proposition `app:ch_seed:prop:seed-strata`: a cube vector in the kernel
forces the covector itself to lie on the same node line. -/
theorem cubePencil_mulVec_cubeVector_eq_zero_iff {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) (ξ : Euclidean n) :
    (cubePencil ξ).mulVec (fun i ↦ cubeVector a b i) = 0 ↔
      ξ = ((∑ j, ξ j) / ((n : ℝ) - 4)) • cubeVector a b := by
  have hd : (n : ℝ) - 4 ≠ 0 := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : cubeCoefficient n * (∑ j, ξ j) * ((n : ℝ) - 4) =
      (∑ j, ξ j) / ((n : ℝ) - 4) := by
    dsimp [cubeCoefficient]
    field_simp
  constructor
  · intro hk
    ext i
    have hi := congrFun hk i
    rw [node_mulVec_apply, node_vector_sum, hc] at hi
    change ξ i * cubeVector a b i - (∑ j, ξ j) / ((n : ℝ) - 4) = 0 at hi
    change ξ i = ((∑ j, ξ j) / ((n : ℝ) - 4)) * cubeVector a b i
    have hsq := node_vector_sq hab i
    linear_combination cubeVector a b i * hi - ξ i * hsq
  · intro heq
    funext i
    rw [node_mulVec_apply, node_vector_sum, hc]
    have hi := congrArg (fun v : Euclidean n ↦ v i) heq
    change ξ i = ((∑ j, ξ j) / ((n : ℝ) - 4)) * cubeVector a b i at hi
    rw [hi]
    change _ = (0 : ℝ)
    have hsq := node_vector_sq hab i
    linear_combination ((∑ j, ξ j) / ((n : ℝ) - 4)) * hsq

/-- Proposition `app:ch_seed:prop:seed-strata`: if a nonzero common quadratic
zero is a kernel vector, the covector is proportional to that vector, with
the exact ratio of coordinate sums from the manuscript. -/
theorem cubePencil_covector_eq_smul_of_common_zero {n : ℕ} (hn : 5 ≤ n)
    {ξ v : Euclidean n} (hv : v ≠ 0)
    (hq : ∀ i, v i ^ 2 - cubeCoefficient n * (∑ j, v j) ^ 2 = 0)
    (hk : (cubePencil ξ).mulVec (fun i ↦ v i) = 0) :
    ξ = ((∑ j, ξ j) / (∑ j, v j)) • v := by
  obtain ⟨a, b, hab, t, rfl⟩ := (cube_quadratic_zero_iff_node hn hv).mp hq
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at hv
  have hk' : (cubePencil ξ).mulVec (fun i ↦ cubeVector a b i) = 0 := by
    change (cubePencil ξ).mulVec (t • (fun i ↦ cubeVector a b i)) = 0 at hk
    rw [Matrix.mulVec_smul] at hk
    exact (smul_eq_zero.mp hk).resolve_left ht
  have hξ := (cubePencil_mulVec_cubeVector_eq_zero_iff hn hab ξ).mp hk'
  have hs : ∑ j, (t • cubeVector a b) j = t * ((n : ℝ) - 4) := by
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, node_vector_sum]
  rw [hs, smul_smul]
  convert hξ using 2
  field_simp

/-- Proposition `app:ch_seed:prop:seed-strata`: the adjugate at a nonzero
node has the rank-one form along its cube vector. This is an actual
factorization, with no factorization hypothesis. -/
theorem cubePencil_node_adjugate {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) :
    ∃ r : ℝ, ∀ i j, (cubePencil (t • cubeVector a b)).adjugate i j =
      r * cubeVector a b i * cubeVector a b j := by
  let M := cubePencil (t • cubeVector a b)
  have hdet : M.det = 0 := cubeDeterminant_node_eq_zero hn hab ht
  have hcol (j : Fin n) : M.mulVec (fun i ↦ M.adjugate i j) = 0 := by
    have hm : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    funext i
    exact congrArg (fun A : MetricTensor n ↦ A i j) hm
  have hex (j : Fin n) : ∃ s : ℝ, (fun i ↦ M.adjugate i j) =
      s • (fun i ↦ cubeVector a b i) :=
    (cubePencil_node_mulVec_eq_zero_iff hn hab ht _).mp (hcol j)
  choose s hs using hex
  have hentry (i j : Fin n) : M.adjugate i j = s j * cubeVector a b i :=
    congrFun (hs j) i
  have hsymm : M.IsSymm := by
    ext i j
    dsimp [M, cubePencil]
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij]
  have ha : cubeVector a b a = -1 := by norm_num [cubeVector, hab]
  have hs' (j : Fin n) : s j = -(s a) * cubeVector a b j := by
    have heq := hsymm.adjugate.apply a j
    rw [hentry, hentry, ha] at heq
    linarith
  refine ⟨-(s a), ?_⟩
  intro i j
  rw [hentry, hs']
  ring

/-- Proposition `app:ch_seed:prop:seed-strata`: the determinant differential
vanishes at every nonzero node, using its proved adjugate factorization. -/
theorem fderiv_cubeDeterminant_node_eq_zero {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) :
    fderiv ℝ cubeDeterminant (t • cubeVector a b) = 0 := by
  obtain ⟨r, hr⟩ := cubePencil_node_adjugate hn hab ht
  have hf : (cubePencil (t • cubeVector a b)).adjugate =
      fun i j ↦ r * cubeVector a b i * cubeVector a b j := by
    ext i j
    exact hr i j
  have hq : cubeQuadraticContraction (cubeVector a b) = 0 := by
    simpa using cubeQuadraticContraction_smul_cubeVector hn hab 1
  rw [fderiv_cubeDeterminant_of_adjugate_eq _ _ r hf, hq]
  simp

/-- Proposition `app:ch_seed:prop:seed-strata`: every coordinate of the
determinant gradient vanishes at a nonzero node. -/
theorem partialDeriv_cubeDeterminant_node_eq_zero {n : ℕ} (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) (i : Fin n) :
    partialDeriv cubeDeterminant (t • cubeVector a b) i = 0 := by
  simp [partialDeriv, fderiv_cubeDeterminant_node_eq_zero hn hab ht]

/-- Proposition `app:ch_seed:prop:seed-strata`: every nonzero common
quadratic zero is a corank-one point of the determinant's singular locus. -/
theorem cubeQuadraticContraction_zero_corank_one_and_singular {n : ℕ} (hn : 5 ≤ n)
    {ξ : Euclidean n} (hξ : ξ ≠ 0) (hq : cubeQuadraticContraction ξ = 0) :
    Module.finrank ℝ (LinearMap.ker (cubePencil ξ).mulVecLin) = 1 ∧
      cubeDeterminant ξ = 0 ∧ fderiv ℝ cubeDeterminant ξ = 0 := by
  obtain ⟨a, b, hab, t, rfl⟩ := (cubeQuadraticContraction_eq_zero_iff_node hn hξ).mp hq
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at hξ
  exact ⟨cubePencil_node_corank hn hab ht, cubeDeterminant_node_eq_zero hn hab ht,
    fderiv_cubeDeterminant_node_eq_zero hn hab ht⟩

end JanetCartan
