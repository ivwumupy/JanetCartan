module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Construction.Center
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Kernel
import Mathlib.Tactic.FieldSimp

/-! The explicit analytic cube bending and its actual center normal map.

The rank and kernel use the checked results of Proposition
`app:ch_seed:prop:seed-gram`; no existence placeholder is used.
-/

@[expose] public noncomputable section

namespace JanetCartan.ReferenceConstruction

/-- Proposition `app:ch_seed:prop:seed-analytic`: Normalize each cube direction by the square root
of the dimension. -/
def unitCubeVector {n : ℕ} (p : CoordinatePair n) : Euclidean n :=
  (Real.sqrt n)⁻¹ • cubeVector p.val.1 p.val.2

/-- Proposition `app:ch_seed:prop:seed-analytic`: The normalized cube direction is a unit vector. -/
theorem unitCubeVector_norm {n : ℕ} (hn : 0 < n) (p : CoordinatePair n) :
    ‖unitCubeVector p‖ = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : ‖cubeVector p.val.1 p.val.2‖ = Real.sqrt n := by
    rw [← cubeVector_norm_sq (ne_of_lt p.property), Real.sqrt_sq (norm_nonneg _)]
  rw [unitCubeVector, norm_smul, hnorm, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.mpr hn'), inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hn'))]

/-- Proposition `app:ch_seed:prop:seed-analytic`: Frequency n cancels the two square-root
normalization factors. -/
theorem unitCubeVector_rankOne {n : ℕ} (hn : 0 < n) (p : CoordinatePair n)
    (u w : Euclidean n) :
    (n : ℝ) * inner ℝ (unitCubeVector p) u * inner ℝ (unitCubeVector p) w =
      inner ℝ (cubeVector p.val.1 p.val.2) u * inner ℝ (cubeVector p.val.1 p.val.2) w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (le_of_lt hn')
  have hsne := ne_of_gt (Real.sqrt_pos.mpr hn')
  simp only [unitCubeVector, real_inner_smul_left]
  field_simp
  rw [hs]

/-- Proposition `app:ch_seed:prop:seed-analytic`: Enumerate the cube directions in a fixed order;
later unused directions are zero. -/
def cubeDirections (n : ℕ) (j : ℕ) : Euclidean n :=
  if h : j < Fintype.card (CoordinatePair n) then
    unitCubeVector ((Fintype.equivFin (CoordinatePair n)).symm ⟨j, h⟩)
  else 0

/-- Proposition `app:ch_seed:prop:seed-analytic`: Every direction used by the finite cube
construction is a unit vector. -/
theorem cubeDirections_norm {n : ℕ} (hn : 0 < n) {j : ℕ}
    (hj : j < Fintype.card (CoordinatePair n)) : ‖cubeDirections n j‖ = 1 := by
  simp only [cubeDirections, dite_eq_left hj]
  exact unitCubeVector_norm hn _

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit composition of all cube circular
bendings. -/
def cubeBending (n : ℕ) : Euclidean n → Euclidean (n + Fintype.card (CoordinatePair n)) :=
  iteratedBending (cubeDirections n) n (Fintype.card (CoordinatePair n))

/-- Proposition `app:ch_seed:prop:seed-analytic`: The cube bending is globally real analytic. -/
theorem cubeBending_analyticOnNhd (n : ℕ) : AnalyticOnNhd ℝ (cubeBending n) Set.univ :=
  iteratedBending_analyticOnNhd _ _ _

/-- Proposition `app:ch_seed:prop:seed-analytic`: The cube bending fixes the center. -/
@[simp] theorem cubeBending_zero (n : ℕ) : cubeBending n 0 = 0 :=
  iteratedBending_zero _ _ _

/-- Proposition `app:ch_seed:prop:seed-analytic`: The explicit cube bending has exactly the flat
metric everywhere. -/
theorem cubeBending_inducedMetric {n : ℕ} (hn : 0 < n) (x : Euclidean n) :
    inducedMetric (cubeBending n) x = 1 :=
  iteratedBending_inducedMetric _ (by exact_mod_cast (Nat.ne_of_gt hn)) _
    (fun _ hj ↦ cubeDirections_norm hn hj) x

/-- Proposition `app:ch_seed:prop:seed-analytic`: Each actual center second form is the prescribed
cube rank-one form. -/
theorem cubeBending_secondFundamentalForm_row {n : ℕ} (hn : 0 < n)
    (p : CoordinatePair n) (i j : Fin n) :
    inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
      (Fintype.equivFin (CoordinatePair n) p))
      (secondFundamentalForm (cubeBending n) 0 i j) =
      cubeVector p.val.1 p.val.2 i * cubeVector p.val.1 p.val.2 j := by
  unfold cubeBending
  rw [iteratedBending_secondFundamentalForm_zero _ (by exact_mod_cast (Nat.ne_of_gt hn)),
    inner_centerNormal_centerSecondJet]
  have hp := (Fintype.equivFin (CoordinatePair n) p).isLt
  simp only [cubeDirections, dite_eq_left hp]
  rw [unitCubeVector_rankOne hn]
  simp [EuclideanSpace.inner_single_right]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual center normal map has exactly the rows
of the cube normal map. -/
theorem cubeBending_normalMap_row {n : ℕ} (hn : 0 < n)
    (p : CoordinatePair n) (H : MetricTensor n) :
    inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
      (Fintype.equivFin (CoordinatePair n) p)) (normalMap (cubeBending n) 0 H) =
      cubeNormalMap n H p := by
  simp [normalMap, inner_sum, real_inner_smul_right,
    cubeBending_secondFundamentalForm_row hn, cubeNormalMap, mul_assoc]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual center normal map takes values in the
normal space. -/
theorem cubeBending_normalMap_mem_normalSpace (n : ℕ) (H : MetricTensor n) :
    normalMap (cubeBending n) 0 H ∈ normalSpace (cubeBending n) 0 := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Subtype.coe_prop _)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The cube-indexed center frame determines every
normal vector. -/
theorem cubeBending_normal_ext {n : ℕ} (hn : 0 < n)
    {z w : Euclidean (n + Fintype.card (CoordinatePair n))}
    (hz : z ∈ normalSpace (cubeBending n) 0) (hw : w ∈ normalSpace (cubeBending n) 0)
    (h : ∀ p : CoordinatePair n,
      inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
        (Fintype.equivFin (CoordinatePair n) p)) z =
      inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
        (Fintype.equivFin (CoordinatePair n) p)) w) : z = w := by
  apply eq_of_inner_centerNormal_eq (cubeDirections n)
    (by exact_mod_cast (Nat.ne_of_gt hn)) _ hz hw
  intro a
  simpa using h ((Fintype.equivFin (CoordinatePair n)).symm a)

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual center normal map and the cube normal
map have the same kernel. -/
theorem cubeBending_normalMap_eq_zero_iff {n : ℕ} (hn : 0 < n) (H : MetricTensor n) :
    normalMap (cubeBending n) 0 H = 0 ↔ cubeNormalMap n H = 0 := by
  constructor
  · intro h
    ext p
    rw [← cubeBending_normalMap_row hn, h, inner_zero_right]
    rfl
  · intro h
    apply cubeBending_normal_ext hn (cubeBending_normalMap_mem_normalSpace n H)
      (Submodule.zero_mem _)
    intro p
    rw [cubeBending_normalMap_row hn, h, inner_zero_right]
    rfl

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual center normal map is onto the entire
normal space. -/
theorem cubeBending_fullNormalRank_zero {n : ℕ} (hn : 5 ≤ n) :
    Set.range (normalMap (cubeBending n) 0) = (normalSpace (cubeBending n) 0 : Set _) := by
  have hn₀ : 0 < n := by omega
  ext z
  constructor
  · rintro ⟨H, rfl⟩
    exact cubeBending_normalMap_mem_normalSpace n H
  · intro hz
    let c : EuclideanSpace ℝ (CoordinatePair n) := WithLp.toLp 2 fun p ↦
      inner ℝ (centerNormal n (Fintype.card (CoordinatePair n))
        (Fintype.equivFin (CoordinatePair n) p)) z
    obtain ⟨H, _, hH⟩ := cubeNormalMap_surjective hn c
    refine ⟨H, cubeBending_normal_ext hn₀ (cubeBending_normalMap_mem_normalSpace n H) hz ?_⟩
    intro p
    rw [cubeBending_normalMap_row hn₀, hH]

/-- Proposition `app:ch_seed:prop:seed-analytic`: The actual center stress space is exactly the
frozen cube stress span. -/
theorem cubeBending_stressSpace_zero {n : ℕ} (hn : 5 ≤ n) :
    stressSpace (cubeBending n) 0 =
      (Submodule.span ℝ (Set.range (cubeStress n)) : Set (MetricTensor n)) := by
  have hn₀ : 0 < n := by omega
  ext H
  change (H.IsSymm ∧ normalMap (cubeBending n) 0 H = 0) ↔ _
  rw [cubeBending_normalMap_eq_zero_iff hn₀]
  constructor
  · rintro ⟨hsymm, h⟩
    exact (cubeNormalMap_eq_zero_iff_mem_span hn H hsymm).mp h
  · intro h
    have hle : Submodule.span ℝ (Set.range (cubeStress n)) ≤ symmetricTensorSubmodule n := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact cubeStress_isSymm i
    have hsymm : H.IsSymm := hle h
    exact ⟨hsymm, (cubeNormalMap_eq_zero_iff_mem_span hn H hsymm).mpr h⟩

/-- Proposition `app:ch_seed:prop:seed-analytic`: The number of tangent and normal coordinates is
the Janet–Cartan dimension. -/
theorem cubeBending_ambientDimension (n : ℕ) :
    n + Fintype.card (CoordinatePair n) = embeddingDimension n := by
  have h := finrank_symmetricTensor_eq_add_cubeNormal n
  rw [finrank_symmetricTensor_eq_embeddingDimension, finrank_euclideanSpace,
    Fintype.card_fin] at h
  exact h.symm

end JanetCartan.ReferenceConstruction
