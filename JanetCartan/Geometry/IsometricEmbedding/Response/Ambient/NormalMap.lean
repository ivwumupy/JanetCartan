module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Projection
public import JanetCartan.Geometry.IsometricEmbedding.Response.Ambient.TensorFrame
public import JanetCartan.LinearAlgebra.NormalInverse

/-!
# Bundling the geometric normal map

The actual map and adjoint used in `main:eq:normal-completion`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.AmbientResponse

/-- The actual normal map, bundled linearly for `main:eq:normal-completion`. -/
def normalMapLinear {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    MetricTensor n →ₗ[ℝ] Euclidean N where
  toFun := normalMap F x
  map_add' A B := by
    simp [normalMap, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [normalMap, mul_smul, Finset.smul_sum]

/-- The normal map with its actual normal-space codomain
(`main:eq:normal-completion`). -/
def normalMapToNormal {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    MetricTensor n →ₗ[ℝ] normalSpace F x :=
  (normalMapLinear F x).codRestrict _ (normalMap_mem_normalSpace F x)

/-- Full normal rank gives actual surjectivity, the hypothesis required by
`NormalInverse` in `main:eq:normal-completion`. -/
theorem normalMapToNormal_surjective {n N : ℕ} {F : Euclidean n → Euclidean N}
    {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    Function.Surjective (normalMapToNormal F x) := by
  intro y
  have hy : (y : Euclidean N) ∈ Set.range (normalMap F x) := by
    rw [hrank]
    exact y.property
  obtain ⟨H, hH⟩ := hy
  exact ⟨H, Subtype.ext hH⟩

/-- The adjoint is exactly the second-form pairing, with the manuscript's
Frobenius normalization (`main:eq:normal-completion`). -/
theorem adjoint_normalMapToNormal {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (w : normalSpace F x) :
    (normalMapToNormal F x).adjoint w = normalPairing F (fun _ ↦ w) x := by
  apply ext_inner_right ℝ
  intro H
  rw [LinearMap.adjoint_inner_left]
  change inner ℝ (w : Euclidean N) (normalMap F x H) =
    tensorPairing (normalPairing F (fun _ ↦ w) x) H
  rw [inner_normalMap_eq_tensorPairing F (fun _ ↦ w)]
  exact real_inner_comm _ H

/-- The pointwise canonical normal completion `(BB*)⁻¹B` from
`main:eq:normal-completion`. It is set to zero away from full normal rank;
all geometric uses below are on the full-rank locus. -/
def canonicalNormalCompletion {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : MetricTensor n →ₗ[ℝ] Euclidean N :=
  if hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)) then
    (normalSpace F x).subtype.comp
      (NormalInverse.normalCompletion (normalMapToNormal F x)
        (normalMapToNormal_surjective hrank))
  else 0

/-- The canonical completion is an actual normal vector
(`main:eq:normal-completion`). -/
theorem canonicalNormalCompletion_mem_normalSpace {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n) (H : MetricTensor n) :
    canonicalNormalCompletion F x H ∈ normalSpace F x := by
  unfold canonicalNormalCompletion
  split
  · exact Subtype.coe_prop _
  · exact Submodule.zero_mem _

/-- The canonical inverse solves the geometric normal equation with its actual
second-form pairing (`main:eq:normal-completion`). -/
theorem canonicalNormalCompletion_normal_equation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : MetricTensor n) :
    normalMap F x (normalPairing F (fun _ ↦ canonicalNormalCompletion F x H) x) =
      normalMap F x H := by
  rw [canonicalNormalCompletion, dite_eq_left hrank]
  change normalMap F x (normalPairing F
    (fun _ ↦ (NormalInverse.normalCompletion (normalMapToNormal F x)
      (normalMapToNormal_surjective hrank) H : Euclidean N)) x) = _
  rw [← adjoint_normalMapToNormal]
  exact congrArg Subtype.val (NormalInverse.normalOperator_inverse_apply
    (normalMapToNormal F x) (normalMapToNormal_surjective hrank) (normalMapToNormal F x H))

end JanetCartan.AmbientResponse
