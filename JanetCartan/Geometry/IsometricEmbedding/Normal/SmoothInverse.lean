module

public import JanetCartan.LinearAlgebra.NormalInverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth canonical inverses of surjective normal maps

For `app:ch_waves:eq:ambient-normal-inverse` in `paper.tex`, this module lifts
`JanetCartan.NormalInverse` to families of operators between fixed finite-dimensional
real inner product spaces. The surjective locus is the open inverse image of the units
under `B ↦ BB*`. On this locus, inversion in the operator algebra gives a smooth
canonical right inverse `B*(BB*)⁻¹` and the smooth orthogonal projector onto `ker B`.
The formulas agree with the existing pointwise linear-map constructions.

The family theorems apply to every differentiability order, including `∞`, and to
joint parameter spaces. This is the qualitative inverse-smoothness step underlying
`app:ch_regular_base:lem:buffered-interpolation`; it makes no quantitative high-jet
estimate. The target space here is a fixed normal space (or a fixed trivialization).
Constructing a varying immersion's ambient normal operator with its tangent summand
is a separate geometric step.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.NormalInverse

variable {E F X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The continuous operator `BB*` on the normal space in
`app:ch_waves:eq:ambient-normal-inverse`. -/
def continuousNormalOperator (B : E →L[ℝ] F) : F →L[ℝ] F := B.comp B.adjoint

/-- The formula `B*(BB*)⁻¹` from `app:ch_waves:eq:ambient-normal-inverse`,
using ring inversion. It is a right inverse on the surjective locus. -/
def continuousRightInverse (B : E →L[ℝ] F) : F →L[ℝ] E :=
  B.adjoint.comp (Ring.inverse (continuousNormalOperator B))

/-- The stress-projector formula `I - B*(BB*)⁻¹B` from
`app:ch_waves:eq:ambient-normal-inverse`, defined on the whole operator space. -/
def continuousKernelProjection (B : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (continuousRightInverse B).comp B

/-- Compatibility of `BB*` with the pointwise construction in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem continuousNormalOperator_toLinearMap (B : E →L[ℝ] F) :
    (continuousNormalOperator B).toLinearMap = normalOperator B.toLinearMap := rfl

/-- The inverse domain in `app:ch_waves:eq:ambient-normal-inverse` is exactly
the surjective locus: `BB*` is a unit if and only if `B` is surjective. -/
theorem continuousNormalOperator_isUnit_iff (B : E →L[ℝ] F) :
    IsUnit (continuousNormalOperator B) ↔ Function.Surjective B := by
  constructor
  · intro h
    have hb := (ContinuousLinearMap.isUnit_iff_bijective.mp h).2
    intro y
    obtain ⟨z, hz⟩ := hb y
    exact ⟨B.adjoint z, hz⟩
  · intro hB
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
      continuousNormalOperator_toLinearMap]
    exact normalOperator_isUnit B.toLinearMap hB

/-- Adjunction is smooth over the reals, as used in the formulas of
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiff_adjoint {k : ℕ∞ω} :
    ContDiff ℝ k (fun B : E →L[ℝ] F ↦ B.adjoint) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).contDiff

/-- The map `B ↦ BB*` is smooth, the first step of inverse smoothness in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiff_continuousNormalOperator {k : ℕ∞ω} :
    ContDiff ℝ k (continuousNormalOperator : (E →L[ℝ] F) → F →L[ℝ] F) :=
  contDiff_id.clm_comp contDiff_adjoint

/-- The surjective locus is open, by pulling back the open unit domain under
`B ↦ BB*`; this supplies the inverse domain for
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem isOpen_surjective : IsOpen {B : E →L[ℝ] F | Function.Surjective B} := by
  have h := Units.isOpen.preimage
    (contDiff_continuousNormalOperator (E := E) (F := F) (k := ∞)).continuous
  simpa only [Set.preimage_ofPred_eq, continuousNormalOperator_isUnit_iff] using h

/-- Ring inversion gives the same `(BB*)⁻¹` as the pointwise linear equivalence
in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem inverse_continuousNormalOperator_toLinearMap (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    (Ring.inverse (continuousNormalOperator B)).toLinearMap =
      normalOperatorInverse B.toLinearMap hB := by
  ext y
  apply (normalOperator_bijective B.toLinearMap hB).1
  have hi := congrArg (fun A : F →L[ℝ] F ↦ A y)
    (Ring.mul_inverse_cancel (continuousNormalOperator B)
      ((continuousNormalOperator_isUnit_iff B).mpr hB))
  exact hi.trans (normalOperator_inverse_apply B.toLinearMap hB y).symm

/-- The smooth formula agrees with `NormalInverse.rightInverse`, the actual
canonical right inverse in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem continuousRightInverse_toLinearMap (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    (continuousRightInverse B).toLinearMap = rightInverse B.toLinearMap hB := by
  change B.toLinearMap.adjoint ∘ₗ (Ring.inverse (continuousNormalOperator B)).toLinearMap = _
  rw [inverse_continuousNormalOperator_toLinearMap]
  rfl

/-- The continuous projector formula agrees with the pointwise construction
in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem continuousKernelProjection_toLinearMap (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    (continuousKernelProjection B).toLinearMap = kernelProjection B.toLinearMap hB := by
  change LinearMap.id - (continuousRightInverse B).toLinearMap ∘ₗ B.toLinearMap = _
  rw [continuousRightInverse_toLinearMap B hB]
  rfl

/-- The inverse `(BB*)⁻¹` is smooth on the open surjective locus, using smooth
ring inversion; the qualitative inverse step of
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem contDiffOn_inverse_continuousNormalOperator {k : ℕ∞ω} :
    ContDiffOn ℝ k (fun B : E →L[ℝ] F ↦ Ring.inverse (continuousNormalOperator B))
      {B | Function.Surjective B} := by
  intro B hB
  have hu := (continuousNormalOperator_isUnit_iff B).mpr hB
  have hi : ContDiffAt ℝ k Ring.inverse (continuousNormalOperator B) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  exact hi.comp_contDiffWithinAt B contDiff_continuousNormalOperator.contDiffWithinAt

/-- The actual canonical right inverse `B*(BB*)⁻¹` is smooth on the surjective
locus, as used in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffOn_continuousRightInverse {k : ℕ∞ω} :
    ContDiffOn ℝ k (continuousRightInverse : (E →L[ℝ] F) → F →L[ℝ] E)
      {B | Function.Surjective B} :=
  contDiff_adjoint.contDiffOn.clm_comp contDiffOn_inverse_continuousNormalOperator

/-- The projector formula `I - B*(BB*)⁻¹B` is smooth on the surjective locus,
as used in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffOn_continuousKernelProjection {k : ℕ∞ω} :
    ContDiffOn ℝ k (continuousKernelProjection : (E →L[ℝ] F) → E →L[ℝ] E)
      {B | Function.Surjective B} :=
  contDiffOn_const.sub (contDiffOn_continuousRightInverse.clm_comp contDiffOn_id)

/-- The continuous formula is the orthogonal projector onto `ker B`, as
asserted in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem continuousKernelProjection_eq_starProjection (B : E →L[ℝ] F)
    (hB : Function.Surjective B) :
    continuousKernelProjection B = B.ker.starProjection := by
  ext x
  exact LinearMap.congr_fun
    ((continuousKernelProjection_toLinearMap B hB).trans
      (kernelProjection_eq_starProjection B.toLinearMap hB)) x

/-- The smooth formula satisfies `B(B*(BB*)⁻¹)y = y`, the right-inverse identity
of `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem apply_continuousRightInverse (B : E →L[ℝ] F)
    (hB : Function.Surjective B) (y : F) :
    B (continuousRightInverse B y) = y := by
  have he := LinearMap.congr_fun (continuousRightInverse_toLinearMap B hB) y
  exact (congrArg B he).trans (apply_rightInverse B.toLinearMap hB y)

/-- The right-inverse formula is smooth in a full neighborhood of each
surjective operator, for `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffAt_continuousRightInverse {k : ℕ∞ω} (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : ContDiffAt ℝ k continuousRightInverse B :=
  contDiffOn_continuousRightInverse.contDiffAt (isOpen_surjective.mem_nhds hB)

/-- The kernel-projector formula is smooth in a full neighborhood of each
surjective operator, for `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffAt_continuousKernelProjection {k : ℕ∞ω} (B : E →L[ℝ] F)
    (hB : Function.Surjective B) : ContDiffAt ℝ k continuousKernelProjection B :=
  contDiffOn_continuousKernelProjection.contDiffAt (isOpen_surjective.mem_nhds hB)

/-- A `C^k` surjective operator family has a `C^k` canonical right inverse.
This is the qualitative family assertion underlying
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem contDiffOn_rightInverse_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    {s : Set X} (hB : ContDiffOn ℝ k B s)
    (hsurj : ∀ x ∈ s, Function.Surjective (B x)) :
    ContDiffOn ℝ k (fun x ↦ continuousRightInverse (B x)) s :=
  contDiffOn_continuousRightInverse.comp hB hsurj

/-- A `C^k` surjective operator family has a `C^k` kernel-projector formula,
as used in `app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffOn_kernelProjection_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    {s : Set X} (hB : ContDiffOn ℝ k B s)
    (hsurj : ∀ x ∈ s, Function.Surjective (B x)) :
    ContDiffOn ℝ k (fun x ↦ continuousKernelProjection (B x)) s :=
  contDiffOn_continuousKernelProjection.comp hB hsurj

/-- Pointwise surjectivity and `C^k` regularity suffice for local `C^k`
regularity of the canonical right inverse in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffAt_rightInverse_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    {x : X} (hB : ContDiffAt ℝ k B x) (hsurj : Function.Surjective (B x)) :
    ContDiffAt ℝ k (fun x ↦ continuousRightInverse (B x)) x :=
  (contDiffAt_continuousRightInverse (B x) hsurj).comp x hB

/-- Pointwise surjectivity and `C^k` regularity suffice for local `C^k`
regularity of the kernel projector in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffAt_kernelProjection_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    {x : X} (hB : ContDiffAt ℝ k B x) (hsurj : Function.Surjective (B x)) :
    ContDiffAt ℝ k (fun x ↦ continuousKernelProjection (B x)) x :=
  (contDiffAt_continuousKernelProjection (B x) hsurj).comp x hB

/-- The actual orthogonal projectors onto the kernels of a `C^k` surjective
family form a `C^k` family, as used in
`app:ch_waves:eq:ambient-normal-inverse`. -/
theorem contDiffOn_starProjection_ker_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    {s : Set X} (hB : ContDiffOn ℝ k B s)
    (hsurj : ∀ x ∈ s, Function.Surjective (B x)) :
    ContDiffOn ℝ k (fun x ↦ (B x).ker.starProjection) s := by
  apply (contDiffOn_kernelProjection_family hB hsurj).congr
  intro x hx
  exact (continuousKernelProjection_eq_starProjection (B x) (hsurj x hx)).symm

/-- The existing pointwise `NormalInverse.rightInverse`, promoted to continuous
linear maps, varies `C^k` with any everywhere-surjective `C^k` family.
This identifies the qualitative smooth inverse in
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem contDiff_rightInverse_family {k : ℕ∞ω} {B : X → E →L[ℝ] F}
    (hB : ContDiff ℝ k B) (hsurj : ∀ x, Function.Surjective (B x)) :
    ContDiff ℝ k (fun x ↦
      (rightInverse (B x).toLinearMap (hsurj x)).toContinuousLinearMap) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have he : (fun x ↦ (rightInverse (B x).toLinearMap (hsurj x)).toContinuousLinearMap) =
      (fun x ↦ continuousRightInverse (B x)) := by
    funext y
    ext z
    exact (LinearMap.congr_fun (continuousRightInverse_toLinearMap (B y) (hsurj y)) z).symm
  rw [he]
  exact contDiffAt_rightInverse_family hB.contDiffAt (hsurj x)

end JanetCartan.NormalInverse
