module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Projection
public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Subspace

/-!
# Stability estimates for the actual geometric normal map

The Frobenius tensor inner product and the actual normal map, with its varying
normal-space codomain, used in `main:prop:seed` and
`app:ch_seed:setup:seed-current`. No normal frame or equality of normal spaces
is assumed. The comparison is made by orthogonal projection to a reference
normal space, and the conclusion concerns the actual new normal Gram operator.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.NormalRankStability

/-- `app:ch_seed:setup:seed-current`: use the topology of the chosen
Frobenius norm explicitly when forming operator norms on tensor maps. -/
scoped instance tensorTopology (n : ℕ) : TopologicalSpace (MetricTensor n) :=
  (Matrix.frobeniusSeminormedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- `app:ch_seed:setup:seed-current`: view Frobenius matrices as a
Euclidean array of Euclidean rows, without changing their norm. -/
def tensorCoordinates (n : ℕ) : MetricTensor n →ₗ[ℝ]
    PiLp 2 (fun _ : Fin n ↦ Euclidean n) where
  toFun A := WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `app:ch_seed:setup:seed-current`: the Frobenius inner product,
compatible with the existing Frobenius matrix norm. -/
scoped instance tensorInnerProductSpace (n : ℕ) : InnerProductSpace ℝ (MetricTensor n) where
  inner A B := inner ℝ (tensorCoordinates n A) (tensorCoordinates n B)
  norm_sq_eq_re_inner A := norm_sq_eq_re_inner (tensorCoordinates n A)
  conj_inner_symm A B := inner_conj_symm _ _
  add_left A B C := by simp only [map_add, inner_add_left]
  smul_left A B r := by simp only [map_smul, inner_smul_left]

/-- `app:ch_seed:setup:seed-current`: this inner product is exactly
the manuscript's tensor contraction. -/
theorem tensor_inner_eq_pairing {n : ℕ} (A B : MetricTensor n) :
    inner ℝ A B = tensorPairing A B := by
  change inner ℝ (tensorCoordinates n A) (tensorCoordinates n B) = _
  simp only [PiLp.inner_apply]
  change (∑ i, ∑ j, B i j * A i j) = _
  simp only [tensorPairing, mul_comm]

/-- `main:prop:seed`: the actual ambient normal map as an operator
with the Frobenius tensor norm. -/
def ambientNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    MetricTensor n →L[ℝ] Euclidean N :=
  LinearMap.toContinuousLinearMap
    { toFun := normalMap F x
      map_add' := fun A B ↦ by
        simp [normalMap, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r A ↦ by
        simp [normalMap, mul_smul, Finset.smul_sum] }

/-- `app:ch_seed:setup:seed-current`: `B_F` with codomain the actual
normal space, equipped with its induced Euclidean inner product. -/
def geometricNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    MetricTensor n →L[ℝ] normalSpace F x :=
  (ambientNormalMap F x).codRestrict _ (normalMap_mem_normalSpace F x)

/-- `main:prop:seed`: compare varying normal maps in the fixed reference
normal space by the explicit orthogonal projection. -/
def fixedNormalMap {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (G : Euclidean n → Euclidean N) (y : Euclidean n) :
    MetricTensor n →L[ℝ] normalSpace F x :=
  (normalSpace F x).orthogonalProjectionOnto.comp (ambientNormalMap G y)

/-- `main:prop:seed`: fixed-space comparison factors through the proved
projection identification of the actual normal spaces. -/
theorem fixedNormalMap_eq_projectionBetween {n N : ℕ}
    (F G : Euclidean n → Euclidean N) (x y : Euclidean n) :
    fixedNormalMap F x G y =
      (projectionBetween (normalSpace G y) (normalSpace F x)).comp
        (geometricNormalMap G y) := rfl

/-- `main:prop:seed`: at the reference point the fixed-space map is
exactly the geometric normal map. -/
@[simp] theorem fixedNormalMap_self {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    fixedNormalMap F x F x = geometricNormalMap F x := by
  ext H : 1
  apply Subtype.ext
  exact normalProjection_normalMap F x H

/-- `app:ch_seed:setup:seed-current`: surjectivity of the typed normal
map is exactly the existing definition of full normal rank at a point. -/
theorem normalMap_range_eq_iff_surjective {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)) ↔
      Function.Surjective (geometricNormalMap F x) := by
  constructor
  · intro h w
    have hw : (w : Euclidean N) ∈ Set.range (normalMap F x) := h.symm ▸ w.property
    obtain ⟨H, hH⟩ := hw
    exact ⟨H, Subtype.ext hH⟩
  · intro h
    apply Set.Subset.antisymm
    · rintro _ ⟨H, rfl⟩
      exact normalMap_mem_normalSpace F x H
    · intro w hw
      obtain ⟨H, hH⟩ := h ⟨w, hw⟩
      exact ⟨H, congrArg Subtype.val hH⟩

/-- `main:prop:seed` and `app:ch_seed:setup:seed-current`: a concrete
operator-norm neighborhood preserves full rank and a `κ² / 4` lower bound
for the actual normal Gram operator on the varying normal space. -/
theorem geometric_normal_rank_and_gap_of_close {n N : ℕ}
    (F G : Euclidean n → Euclidean N) (x y : Euclidean n)
    {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ w, κ * ‖w‖ ≤ ‖(geometricNormalMap F x).adjoint w‖)
    (hproj : ‖normalProjection F x - normalProjection G y‖ < 1)
    (hclose : ‖fixedNormalMap F x G y - geometricNormalMap F x‖ ≤ κ / 2) :
    Set.range (normalMap G y) = (normalSpace G y : Set (Euclidean N)) ∧
      ∀ w : normalSpace G y, (κ ^ 2 / 4) * ‖w‖ ^ 2 ≤
        inner ℝ (NormalPerturbation.normal (geometricNormalMap G y) w) w := by
  have h := surjective_and_normal_gap_of_projected_norm_sub_le
    (normalSpace F x) (normalSpace G y) (geometricNormalMap F x)
    (geometricNormalMap G y) hκ hgap hproj hclose
  exact ⟨(normalMap_range_eq_iff_surjective G y).mpr h.1, h.2⟩

/-- `main:prop:seed`: full geometric normal rank supplies the positive
constant for the preceding explicit neighborhood, with no gap assumed. -/
theorem exists_geometric_normal_rank_gap_neighborhood {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (G : Euclidean n → Euclidean N) (y : Euclidean n),
      ‖normalProjection F x - normalProjection G y‖ < 1 →
      ‖fixedNormalMap F x G y - geometricNormalMap F x‖ ≤ κ / 2 →
      Set.range (normalMap G y) = (normalSpace G y : Set (Euclidean N)) ∧
        ∀ w : normalSpace G y, (κ ^ 2 / 4) * ‖w‖ ^ 2 ≤
          inner ℝ (NormalPerturbation.normal (geometricNormalMap G y) w) w := by
  obtain ⟨κ, hκ, hg⟩ := exists_adjoint_lower_bound (geometricNormalMap F x)
    ((normalMap_range_eq_iff_surjective F x).mp hrank)
  exact ⟨κ, hκ, fun G y hp hc ↦ geometric_normal_rank_and_gap_of_close F G x y hκ hg hp hc⟩

end JanetCartan.NormalRankStability
