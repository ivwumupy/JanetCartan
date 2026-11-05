module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Canonical inverses of surjective normal maps

The finite-dimensional linear algebra of `main:eq:normal-completion` and
`app:ch_waves:eq:ambient-normal-inverse` in `paper.tex`. For a surjective real linear map
`B : E →ₗ[ℝ] F`, the normal operator `BB*` is invertible. Its inverse gives the canonical
right inverse `B*(BB*)⁻¹`, the stress projection `I - B*(BB*)⁻¹B` onto `ker B`, and
the inverse of `B* : F → (ker B)ᗮ`.

Here `F` is the normal space itself. These are pointwise algebraic results; smooth
dependence on an immersion and extension to an ambient space with a tangent summand
are separate geometric questions.
-/

@[expose] public noncomputable section

namespace JanetCartan.NormalInverse

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The operator `BB*` on the normal space, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
def normalOperator (B : E →ₗ[ℝ] F) : F →ₗ[ℝ] F := B ∘ₗ B.adjoint

/-- Surjectivity of `B` makes `BB*` bijective, as required in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem normalOperator_bijective (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    Function.Bijective (normalOperator B) := by
  have hs : Function.Surjective (normalOperator B) := by
    rw [← LinearMap.range_eq_top, normalOperator, LinearMap.range_self_comp_adjoint]
    exact LinearMap.range_eq_top.mpr hB
  exact ⟨LinearMap.injective_iff_surjective.mpr hs, hs⟩

/-- Ring-theoretic invertibility of `BB*` in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem normalOperator_isUnit (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    IsUnit (normalOperator B) := by
  rw [LinearMap.isUnit_iff_range_eq_top, LinearMap.range_eq_top]
  exact (normalOperator_bijective B hB).2

/-- `BB*` as a linear equivalence, from `app:ch_waves:eq:ambient-normal-inverse`. -/
def normalOperatorEquiv (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : F ≃ₗ[ℝ] F :=
  LinearEquiv.ofBijective (normalOperator B) (normalOperator_bijective B hB)

/-- The inverse `(BB*)⁻¹`, from `app:ch_waves:eq:ambient-normal-inverse`. -/
def normalOperatorInverse (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : F →ₗ[ℝ] F :=
  (normalOperatorEquiv B hB).symm.toLinearMap

/-- The right inverse identity for `BB*` in `app:ch_waves:eq:ambient-normal-inverse`. -/
@[simp] theorem normalOperator_inverse_apply (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (y : F) :
    normalOperator B (normalOperatorInverse B hB y) = y :=
  (normalOperatorEquiv B hB).apply_symm_apply y

/-- The left inverse identity for `BB*` in `app:ch_waves:eq:ambient-normal-inverse`. -/
@[simp] theorem inverse_normalOperator_apply (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (y : F) :
    normalOperatorInverse B hB (normalOperator B y) = y :=
  (normalOperatorEquiv B hB).symm_apply_apply y

/-- The map identity `BB*(BB*)⁻¹ = I`, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem normalOperator_comp_inverse (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    normalOperator B ∘ₗ normalOperatorInverse B hB = LinearMap.id := by
  ext y
  exact normalOperator_inverse_apply B hB y

/-- The map identity `(BB*)⁻¹BB* = I`, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem inverse_comp_normalOperator (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    normalOperatorInverse B hB ∘ₗ normalOperator B = LinearMap.id := by
  ext y
  exact inverse_normalOperator_apply B hB y

/-- The canonical right inverse `B*(BB*)⁻¹`, used in the stress projection in
`app:ch_waves:eq:ambient-normal-inverse`. -/
def rightInverse (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : F →ₗ[ℝ] E :=
  B.adjoint ∘ₗ normalOperatorInverse B hB

/-- `B*(BB*)⁻¹` is a right inverse of `B`, as used in
`app:ch_waves:eq:ambient-normal-inverse`. -/
@[simp] theorem apply_rightInverse (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (y : F) : B (rightInverse B hB y) = y :=
  normalOperator_inverse_apply B hB y

/-- The map identity `B(B*(BB*)⁻¹) = I`, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem comp_rightInverse (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    B ∘ₗ rightInverse B hB = LinearMap.id := by
  ext y
  exact apply_rightInverse B hB y

/-- The canonical right inverse lands in `(ker B)ᗮ`, the subspace used in
`main:eq:normal-completion`. -/
theorem rightInverse_mem_orthogonal_ker (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (y : F) : rightInverse B hB y ∈ B.kerᗮ := by
  rw [LinearMap.orthogonal_ker]
  exact ⟨normalOperatorInverse B hB y, rfl⟩

/-- The stress projection formula `I - B*(BB*)⁻¹B`, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
def kernelProjection (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : E →ₗ[ℝ] E :=
  LinearMap.id - rightInverse B hB ∘ₗ B

/-- The stress projection formula is the orthogonal projection onto `ker B`, as asserted in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem kernelProjection_eq_starProjection (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) :
    kernelProjection B hB = B.ker.starProjection.toLinearMap := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · change B (x - rightInverse B hB (B x)) = 0
    simp
  · change x - (x - rightInverse B hB (B x)) ∈ B.kerᗮ
    simpa only [sub_sub_cancel] using rightInverse_mem_orthogonal_ker B hB (B x)

/-- The explicit identity `Π_(ker B) = I - B*(BB*)⁻¹B`, from
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem kernelProjection_formula (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) :
    B.ker.starProjection.toLinearMap =
      LinearMap.id - B.adjoint ∘ₗ normalOperatorInverse B hB ∘ₗ B :=
  (kernelProjection_eq_starProjection B hB).symm

/-- `B*(BB*)⁻¹B` is the orthogonal projection onto `(ker B)ᗮ`, as used in
`main:eq:normal-completion`. -/
theorem rightInverse_comp_eq_starProjection_orthogonal (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) :
    rightInverse B hB ∘ₗ B = B.kerᗮ.starProjection.toLinearMap := by
  ext x
  change rightInverse B hB (B x) = B.kerᗮ.starProjection x
  rw [Submodule.starProjection_orthogonal_val]
  have hk := LinearMap.congr_fun (kernelProjection_eq_starProjection B hB) x
  change x - rightInverse B hB (B x) = B.ker.starProjection x at hk
  rw [← hk, sub_sub_cancel]

/-- The normal-completion operator `(BB*)⁻¹B`, extending the inverse of the restricted
adjoint in `main:eq:normal-completion`. -/
def normalCompletion (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : E →ₗ[ℝ] F :=
  normalOperatorInverse B hB ∘ₗ B

/-- Normal completion is a left inverse of `B*`, from `main:eq:normal-completion`. -/
@[simp] theorem normalCompletion_adjoint (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (y : F) :
    normalCompletion B hB (B.adjoint y) = y :=
  inverse_normalOperator_apply B hB y

/-- Applying `B*` after normal completion recovers the orthogonal component, as required by
`main:eq:normal-completion`. -/
theorem adjoint_normalCompletion (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (x : E) :
    B.adjoint (normalCompletion B hB x) = B.kerᗮ.starProjection x :=
  LinearMap.congr_fun (rightInverse_comp_eq_starProjection_orthogonal B hB) x

/-- The restricted adjoint `B* : F ≃ₗ[ℝ] (ker B)ᗮ` from `main:eq:normal-completion`.
Its inverse is explicitly `(BB*)⁻¹B`. -/
def adjointEquiv (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) : F ≃ₗ[ℝ] B.kerᗮ where
  toLinearMap := B.adjoint.codRestrict _ fun y ↦ by
    rw [LinearMap.orthogonal_ker]
    exact ⟨y, rfl⟩
  invFun := fun x ↦ normalCompletion B hB x
  left_inv := normalCompletion_adjoint B hB
  right_inv := fun x ↦ Subtype.ext <| by
    change B.adjoint (normalCompletion B hB x) = x
    rw [adjoint_normalCompletion]
    exact Submodule.starProjection_eq_self_iff.mpr x.property

/-- The equivalence in `main:eq:normal-completion` is the actual adjoint of `B`. -/
@[simp] theorem adjointEquiv_apply (B : E →ₗ[ℝ] F) (hB : Function.Surjective B) (y : F) :
    (adjointEquiv B hB y : E) = B.adjoint y := rfl

/-- The inverse of the restricted adjoint is `(BB*)⁻¹B`, as in the formula preceding
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem adjointEquiv_symm_apply (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (x : B.kerᗮ) :
    (adjointEquiv B hB).symm x = normalOperatorInverse B hB (B x) := rfl

/-- Normal completion equals `(B*)⁻¹ Π_((ker B)ᗮ)`, precisely the pointwise operator in
`main:eq:normal-completion`. -/
theorem normalCompletion_eq_adjointEquiv_symm_projection (B : E →ₗ[ℝ] F)
    (hB : Function.Surjective B) (x : E) :
    normalCompletion B hB x = (adjointEquiv B hB).symm
      (B.kerᗮ.orthogonalProjectionOnto x) := by
  apply (adjointEquiv B hB).injective
  apply Subtype.ext
  simpa using adjoint_normalCompletion B hB x

end JanetCartan.NormalInverse
