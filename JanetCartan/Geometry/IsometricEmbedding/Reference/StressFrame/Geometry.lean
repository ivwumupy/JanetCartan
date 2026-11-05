module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Completion
public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame.Neighborhood

/-!
# The actual projected symmetric stresses

The operators of `app:ch_seed:setup:seed-current`. The ambient inverse is the
one already constructed for normal completion. The stress kernel here is the
kernel on symmetric tensors, not the larger kernel on all matrices.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.AmbientResponse

namespace JanetCartan.ProjectedStressFrame

variable {n N : ℕ} (F : Euclidean n → Euclidean N) (x : Euclidean n)

/-- The actual normal map on `Sym²`, in `app:ch_seed:setup:seed-current`. -/
def symmetricNormalMap : SymmetricTensor n →ₗ[ℝ] normalSpace F x :=
  (normalMapToNormal F x).comp (symmetricTensorSubmodule n).subtype

/-- The symmetric normal map with fixed ambient codomain in
`app:ch_seed:setup:seed-current`. -/
def symmetricAmbientNormalMap : SymmetricTensor n →ₗ[ℝ] Euclidean N :=
  (normalMapLinear F x).comp (symmetricTensorSubmodule n).subtype

/-- The fixed-ambient-space formula `I - B* A⁻¹ B` from
`app:ch_seed:setup:seed-current`, before restricting its domain to `Sym²`. -/
def stressProjection : MetricTensor n →L[ℝ] MetricTensor n :=
  ContinuousLinearMap.id ℝ _ -
    (normalMapLinear F x).adjoint.toContinuousLinearMap.comp
      ((Ring.inverse (ambientNormalOperator F x)).comp
        (normalMapLinear F x).toContinuousLinearMap)

/-- The actual frame `Qᵢ = Π_K Qᵢ⁰` of `app:ch_seed:setup:seed-current`. -/
def projectedStress (i : Fin n) : MetricTensor n :=
  stressProjection F x (cubeStress n i)

/-- The ambient normal operator is exactly `BB* + (I - Pperp)` in
`app:ch_seed:setup:seed-current`. -/
theorem ambientNormalOperator_formula :
    ambientNormalOperator F x =
      ((normalMapLinear F x).comp (normalMapLinear F x).adjoint).toContinuousLinearMap +
        (ContinuousLinearMap.id ℝ _ - normalProjection F x) := by
  ext w
  simp only [ambientNormalOperator, add_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    normalProjection_eq_sub_tangentProjection, sub_sub_cancel]

/-- The formula for `Π_K` applied to an arbitrary tensor, from
`app:ch_seed:setup:seed-current`. -/
theorem stressProjection_apply (H : MetricTensor n) :
    stressProjection F x H = H - normalPairing F
      (fun _ ↦ Ring.inverse (ambientNormalOperator F x) (normalMap F x H)) x := by
  change H - (normalMapLinear F x).adjoint _ = _
  rw [adjoint_normalMapLinear]
  rfl

variable {F x}

/-- The adjoint of the symmetric ambient normal map is the actual pairing in
`app:ch_seed:setup:seed-current`. -/
theorem adjoint_symmetricAmbientNormalMap (hF : ContDiffAt ℝ 2 F x)
    (w : Euclidean N) :
    ((symmetricAmbientNormalMap F x).adjoint w : MetricTensor n) =
      normalPairing F (fun _ ↦ w) x := by
  have h : (symmetricAmbientNormalMap F x).adjoint w =
      (⟨normalPairing F (fun _ ↦ w) x, normalPairing_isSymm _ hF⟩ : SymmetricTensor n) := by
    apply ext_inner_right ℝ
    intro H
    rw [LinearMap.adjoint_inner_left]
    change inner ℝ w (normalMap F x H.val) =
      tensorPairing (normalPairing F (fun _ ↦ w) x) H.val
    rw [inner_normalMap_eq_tensorPairing F (fun _ ↦ w)]
    exact (real_inner_comm H.val (normalPairing F (fun _ ↦ w) x)).symm
  exact congrArg Subtype.val h

/-- The ambient inverse uses exactly `BB*` for the map on symmetric tensors:
extending `B` to all matrices does not change `A_F`
(`app:ch_seed:setup:seed-current`). -/
theorem ambientNormalOperator_eq_symmetric_formula (hF : ContDiffAt ℝ 2 F x) :
    ambientNormalOperator F x =
      ((symmetricAmbientNormalMap F x).comp
        (symmetricAmbientNormalMap F x).adjoint).toContinuousLinearMap +
      (ContinuousLinearMap.id ℝ _ - normalProjection F x) := by
  ext w : 1
  change ambientNormalOperator F x w =
    normalMap F x ((symmetricAmbientNormalMap F x).adjoint w).val +
      (w - normalProjection F x w)
  rw [ambientNormalOperator_apply, adjoint_symmetricAmbientNormalMap hF,
    normalProjection_eq_sub_tangentProjection, sub_sub_cancel]

/-- On the full-rank locus the explicit projection is the normal-completion
formula in `app:ch_seed:setup:seed-current`. -/
theorem stressProjection_eq_sub_completion
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : MetricTensor n) :
    stressProjection F x H = H -
      normalPairing F (fun _ ↦ canonicalNormalCompletion F x H) x := by
  rw [stressProjection_apply, canonicalNormalCompletion_eq_ambient_inverse hrank]

/-- The actual inverse formula lands in the normal-map kernel
(`app:ch_seed:setup:seed-current`). -/
theorem normalMap_stressProjection
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : MetricTensor n) : normalMap F x (stressProjection F x H) = 0 := by
  rw [stressProjection_eq_sub_completion hrank]
  change normalMapLinear F x (H - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (canonicalNormalCompletion_normal_equation hrank H).symm

/-- The projection preserves symmetric tensors, using symmetry of the actual
second form (`app:ch_seed:setup:seed-current`). -/
theorem stressProjection_isSymm (hF : ContDiffAt ℝ 2 F x)
    {H : MetricTensor n} (hH : H.IsSymm) : (stressProjection F x H).IsSymm := by
  rw [stressProjection_apply]
  exact hH.sub (normalPairing_isSymm _ hF)

/-- The adjoint on `Sym²` is the actual second-form pairing, with Frobenius
normalization (`app:ch_seed:setup:seed-current`). -/
theorem adjoint_symmetricNormalMap (hF : ContDiffAt ℝ 2 F x)
    (w : normalSpace F x) :
    ((symmetricNormalMap F x).adjoint w : MetricTensor n) =
      normalPairing F (fun _ ↦ w) x := by
  have h : (symmetricNormalMap F x).adjoint w =
      (⟨normalPairing F (fun _ ↦ w) x, normalPairing_isSymm _ hF⟩ : SymmetricTensor n) := by
    apply ext_inner_right ℝ
    intro H
    rw [LinearMap.adjoint_inner_left]
    change inner ℝ (w : Euclidean N) (normalMap F x H.val) =
      tensorPairing (normalPairing F (fun _ ↦ w) x) H.val
    rw [inner_normalMap_eq_tensorPairing F (fun _ ↦ w)]
    exact (real_inner_comm H.val (normalPairing F (fun _ ↦ w) x)).symm
  exact congrArg Subtype.val h

/-- Full normal rank is still surjectivity after restricting to symmetric
tensors. This discharges the domain issue in `app:ch_seed:setup:seed-current`. -/
theorem symmetricNormalMap_surjective (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    Function.Surjective (symmetricNormalMap F x) := by
  intro w
  obtain ⟨H, hH⟩ := normalMapToNormal_surjective hrank w
  refine ⟨⟨normalPairing F (fun _ ↦ canonicalNormalCompletion F x H) x,
    normalPairing_isSymm _ hF⟩, ?_⟩
  apply Subtype.ext
  exact (canonicalNormalCompletion_normal_equation hrank H).trans
    (congrArg Subtype.val hH)

/-- The ambient rational formula restricts to the orthogonal projection onto
the symmetric stress kernel, as in `app:ch_seed:setup:seed-current`. -/
theorem stressProjection_eq_symmetric_starProjection (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (H : SymmetricTensor n) :
    stressProjection F x H.val =
      ((symmetricNormalMap F x).ker.starProjection H : MetricTensor n) := by
  let Q : SymmetricTensor n := ⟨stressProjection F x H.val,
    stressProjection_isSymm hF H.isSymm⟩
  have hQ : (symmetricNormalMap F x).ker.starProjection H = Q := by
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · change symmetricNormalMap F x Q = 0
      apply Subtype.ext
      exact normalMap_stressProjection hrank H.val
    · rw [LinearMap.orthogonal_ker]
      refine ⟨⟨canonicalNormalCompletion F x H.val,
        canonicalNormalCompletion_mem_normalSpace F x H.val⟩, ?_⟩
      apply Subtype.ext
      rw [adjoint_symmetricNormalMap hF]
      change _ = H.val - stressProjection F x H.val
      rw [stressProjection_eq_sub_completion hrank, sub_sub_cancel]
  exact (congrArg Subtype.val hQ).symm

/-- Identification with the already constructed projected cube stresses,
now for the actual geometric normal map (`app:ch_seed:setup:seed-current`). -/
theorem projectedStress_eq_projectedCubeStress (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (i : Fin n) : projectedStress F x i =
      (StressFrame.projectedCubeStress (symmetricNormalMap F x) i).val :=
  stressProjection_eq_symmetric_starProjection hF hrank (cubeSymmetricStress n i)

/-- The constructed frame consists of symmetric stresses, in the precise
`stressSpace` of `app:ch_seed:setup:seed-current`. -/
theorem projectedStress_mem_stressSpace (hF : ContDiffAt ℝ 2 F x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N)))
    (i : Fin n) : projectedStress F x i ∈ stressSpace F x :=
  ⟨stressProjection_isSymm hF (cubeSymmetricStress n i).isSymm,
    normalMap_stressProjection hrank (cubeStress n i)⟩

/-- In Janet--Cartan ambient dimension, immersion gives exactly the dimension
identity required for the symmetric stress basis in `app:ch_seed:setup:seed-current`. -/
theorem finrank_symmetricTensor_eq_add_normalSpace
    {F : Euclidean n → Euclidean (embeddingDimension n)} {x : Euclidean n}
    (himm : Function.Injective (fderiv ℝ F x)) :
    Module.finrank ℝ (SymmetricTensor n) = n + Module.finrank ℝ (normalSpace F x) := by
  rw [finrank_symmetricTensor_eq_embeddingDimension]
  have ht : Module.finrank ℝ (LinearMap.range (fderiv ℝ F x).toLinearMap) = n := by
    rw [LinearMap.finrank_range_of_inj himm]
    exact finrank_euclideanSpace_fin
  calc
    embeddingDimension n = Module.finrank ℝ (Euclidean (embeddingDimension n)) :=
      finrank_euclideanSpace_fin.symm
    _ = Module.finrank ℝ (LinearMap.range (fderiv ℝ F x).toLinearMap) +
        Module.finrank ℝ (normalSpace F x) :=
      (LinearMap.range (fderiv ℝ F x).toLinearMap).finrank_add_finrank_orthogonal.symm
    _ = n + Module.finrank ℝ (normalSpace F x) := congrArg (· + _) ht

end JanetCartan.ProjectedStressFrame
