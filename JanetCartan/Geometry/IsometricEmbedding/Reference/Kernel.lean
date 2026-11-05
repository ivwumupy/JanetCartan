module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Kernel.LinearAlgebra
public import JanetCartan.Geometry.IsometricEmbedding.Reference.RankOne
public import JanetCartan.Geometry.IsometricEmbedding.Reference.CubeVectors
public import JanetCartan.Analysis.Matrix.Symmetric

/-!
# Linear structure of the cube normal map

Surjectivity and the exact stress kernel in Proposition
`app:ch_seed:prop:seed-gram`. Independent rank-one rows give surjectivity;
the independent annihilating stresses exhaust the kernel by rank–nullity
on symmetric tensors.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan

/-- The cube normal map of Proposition `app:ch_seed:prop:seed-gram`, bundled
as a linear map on coordinate tensors. -/
def cubeNormalLinearMap (n : ℕ) :
    MetricTensor n →ₗ[ℝ] EuclideanSpace ℝ (CoordinatePair n) where
  toFun := cubeNormalMap n
  map_add' H K := by
    ext p
    simp [cubeNormalMap, add_mul, Finset.sum_add_distrib]
  map_smul' c H := by
    ext p
    simp [cubeNormalMap, mul_assoc, Finset.mul_sum]

/-- Evaluation of the bundled cube map; Proposition `app:ch_seed:prop:seed-gram`. -/
@[simp] theorem cubeNormalLinearMap_apply (n : ℕ) (H : MetricTensor n) :
    cubeNormalLinearMap n H = cubeNormalMap n H := rfl

/-- The rows of the cube normal map are the Frobenius rank-one forms from
Proposition `app:ch_seed:prop:seed-gram`. -/
theorem cubeNormalMap_eq_tensorContraction {n : ℕ} (H : MetricTensor n)
    (p : CoordinatePair n) :
    cubeNormalMap n H p = CubeKernel.tensorContraction
      (fun q : CoordinatePair n ↦
        (fun i j ↦ cubeVector q.val.1 q.val.2 i * cubeVector q.val.1 q.val.2 j :
          MetricTensor n)) H p := by
  simp [cubeNormalMap, CubeKernel.tensorContraction, tensorPairing, mul_assoc]

/-- The surjectivity step of Proposition `app:ch_seed:prop:seed-gram`, assuming
the separate independence result for its rank-one row tensors. -/
theorem cubeNormalMap_surjective_of_rankOne_independent {n : ℕ}
    (hrows : LinearIndependent ℝ (fun p : CoordinatePair n ↦
      (fun i j ↦ cubeVector p.val.1 p.val.2 i * cubeVector p.val.1 p.val.2 j :
        MetricTensor n))) :
    ∀ v : EuclideanSpace ℝ (CoordinatePair n),
      ∃ H : MetricTensor n, H.IsSymm ∧ cubeNormalMap n H = v := by
  intro v
  obtain ⟨H, hsymm, hH⟩ := CubeKernel.exists_isSymm_tensorContraction_eq _ hrows
    (fun _ ↦ Matrix.IsSymm.ext (fun _ _ ↦ mul_comm _ _)) (fun p ↦ v p)
  refine ⟨H, hsymm, ?_⟩
  ext p
  rw [cubeNormalMap_eq_tensorContraction]
  exact congrFun hH p

/-- Proposition `app:ch_seed:prop:seed-gram`: the cube normal map is onto
already on symmetric tensors. -/
theorem cubeNormalMap_surjective {n : ℕ} (hn : 5 ≤ n) :
    ∀ v : EuclideanSpace ℝ (CoordinatePair n),
      ∃ H : MetricTensor n, H.IsSymm ∧ cubeNormalMap n H = v :=
  cubeNormalMap_surjective_of_rankOne_independent (cubeVector_rankOne_linearIndependent hn)

/-- Definition `app:ch_seed:defn:seed-cube`: the frozen stresses are symmetric. -/
theorem cubeStress_isSymm {n : ℕ} (i : Fin n) : (cubeStress n i).IsSymm := by
  apply Matrix.IsSymm.ext
  intro j k
  simp only [cubeStress, and_comm]

/-- The stress family in the symmetric tensor space of
Definition `app:ch_seed:defn:seed-cube`. -/
def cubeSymmetricStress (n : ℕ) (i : Fin n) : SymmetricTensor n :=
  ⟨cubeStress n i, cubeStress_isSymm i⟩

/-- Proposition `app:ch_seed:prop:seed-gram`: the bundled stresses are independent. -/
theorem cubeSymmetricStress_linearIndependent {n : ℕ} (hn : 5 ≤ n) :
    LinearIndependent ℝ (cubeSymmetricStress n) :=
  (cubeStress_linearIndependent hn).of_comp (symmetricTensorSubmodule n).subtype

/-- The map `B₀` on the symmetric tensor space in
Proposition `app:ch_seed:prop:seed-gram`. -/
def cubeNormalLinearMapOnSymmetric (n : ℕ) :
    SymmetricTensor n →ₗ[ℝ] EuclideanSpace ℝ (CoordinatePair n) :=
  (cubeNormalLinearMap n).comp (symmetricTensorSubmodule n).subtype

/-- Proposition `app:ch_seed:prop:seed-gram`: surjectivity of the bundled map `B₀`. -/
theorem cubeNormalLinearMapOnSymmetric_surjective {n : ℕ} (hn : 5 ≤ n) :
    Function.Surjective (cubeNormalLinearMapOnSymmetric n) := by
  intro v
  obtain ⟨H, hsymm, hH⟩ := cubeNormalMap_surjective hn v
  exact ⟨⟨H, hsymm⟩, hH⟩

/-- The dimension identity `N = n + q` used for the exact kernel in
Proposition `app:ch_seed:prop:seed-gram`. -/
theorem finrank_symmetricTensor_eq_add_cubeNormal (n : ℕ) :
    Module.finrank ℝ (SymmetricTensor n) =
      Fintype.card (Fin n) + Module.finrank ℝ (EuclideanSpace ℝ (CoordinatePair n)) := by
  rw [finrank_symmetricTensor, finrank_euclideanSpace, Fintype.card_fin,
    coordinatePair_card_choose]
  have h : (n + 1).choose 2 = n + n.choose 2 := by
    simpa using Nat.choose_succ_succ n 1
  simpa only [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm] using h

/-- Proposition `app:ch_seed:prop:seed-gram`: the kernel of `B₀` on symmetric
tensors is exactly the span of its frozen stresses. -/
theorem cubeNormalLinearMapOnSymmetric_ker {n : ℕ} (hn : 5 ≤ n) :
    LinearMap.ker (cubeNormalLinearMapOnSymmetric n) =
      Submodule.span ℝ (Set.range (cubeSymmetricStress n)) := by
  exact CubeKernel.ker_eq_span_of_finrank _ _ (cubeSymmetricStress_linearIndependent hn)
    (fun i ↦ cubeNormalMap_cubeStress hn i)
    (cubeNormalLinearMapOnSymmetric_surjective hn)
    (finrank_symmetricTensor_eq_add_cubeNormal n)

/-- Proposition `app:ch_seed:prop:seed-gram`: a symmetric tensor is annihilated
by the cube normal map exactly when it belongs to the ambient stress span. -/
theorem cubeNormalMap_eq_zero_iff_mem_span {n : ℕ} (hn : 5 ≤ n)
    (H : MetricTensor n) (hsymm : H.IsSymm) :
    cubeNormalMap n H = 0 ↔ H ∈ Submodule.span ℝ (Set.range (cubeStress n)) := by
  let S : SymmetricTensor n := ⟨H, hsymm⟩
  change S ∈ LinearMap.ker (cubeNormalLinearMapOnSymmetric n) ↔ _
  rw [cubeNormalLinearMapOnSymmetric_ker hn]
  have hspan := Submodule.apply_mem_span_image_iff_mem_span
    (f := (symmetricTensorSubmodule n).subtype) (x := S)
    (s := Set.range (cubeSymmetricStress n))
    (symmetricTensorSubmodule n).injective_subtype
  simpa only [← Set.range_comp, Function.comp_def, Submodule.subtype_apply,
    cubeSymmetricStress] using hspan.symm

/-- Proposition `app:ch_seed:prop:seed-gram`: independence of the frozen stresses,
full normal rank, and the exact stress kernel. This proves the full conclusion
consumed by the public `cube_normal_rank_and_kernel` theorem. -/
theorem cubeNormalMap_rank_and_kernel {n : ℕ} (hn : 5 ≤ n) :
    LinearIndependent ℝ (cubeStress n) ∧
    (∀ v : EuclideanSpace ℝ (CoordinatePair n),
      ∃ H : MetricTensor n, H.IsSymm ∧ cubeNormalMap n H = v) ∧
    ∀ H : MetricTensor n, H.IsSymm →
      (cubeNormalMap n H = 0 ↔ H ∈ Submodule.span ℝ (Set.range (cubeStress n))) :=
  ⟨cubeStress_linearIndependent hn, cubeNormalMap_surjective hn,
    cubeNormalMap_eq_zero_iff_mem_span hn⟩

end JanetCartan
