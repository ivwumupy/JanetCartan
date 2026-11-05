module

public import JanetCartan.LinearAlgebra.NormalInverse
public import JanetCartan.LinearAlgebra.GramProjection
import Mathlib.Tactic.Abel

/-!
# Algebra of the single current-mean normal correction

The pointwise algebra in `main:eq:mean-normal-field` of paper.tex. The inverse
is the canonical inverse constructed from a surjective normal map. Identifying
this map with the second fundamental form, proving smoothness, and estimating
the resulting fields remain geometric and analytic tasks.
-/

@[expose] public noncomputable section

namespace JanetCartan.CurrentMean

open scoped InnerProductSpace

variable {T V : Type*}
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `main:eq:mean-normal-field`: the one normal correction, with the factor
`-1/2`, using `(BB*)⁻¹B` on the full tensor defect. -/
def normalCorrection (B : T →ₗ[ℝ] V) (hB : Function.Surjective B) (defect : T) : V :=
  -(1 / 2 : ℝ) • NormalInverse.normalCompletion B hB defect

/-- `main:eq:mean-normal-field`: the normal strain of the correction removes
exactly the component orthogonal to the stress kernel. -/
theorem normalCorrection_strain (B : T →ₗ[ℝ] V) (hB : Function.Surjective B)
    (defect : T) :
    (-2 : ℝ) • B.adjoint (normalCorrection B hB defect) = B.kerᗮ.starProjection defect := by
  simp only [normalCorrection, map_smul, smul_smul, NormalInverse.adjoint_normalCompletion]
  norm_num

/-- `main:eq:mean-equation`: after the single normal correction, the full
tensor error has the manuscript's sign `-Π_(ker B) T_f`. -/
theorem completedTensor_error (B : T →ₗ[ℝ] V) (hB : Function.Surjective B)
    (strain selfTensor target : T) :
    strain + (-2 : ℝ) • B.adjoint
        (normalCorrection B hB (target - strain - selfTensor)) + selfTensor - target =
      -B.ker.starProjection (target - strain - selfTensor) := by
  rw [normalCorrection_strain, Submodule.starProjection_orthogonal_val]
  abel

/-- `main:eq:mean-equation`: when the frame spans the stress kernel, the
remaining tensor error is the inverse-Gram reconstruction of the reduced
defect, with a minus sign and no additional normal completion. -/
theorem completedTensor_error_eq_inverseGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : T →ₗ[ℝ] V) (hB : Function.Surjective B) (v : ι → T)
    (hv : LinearIndependent ℝ v) (hspan : Submodule.span ℝ (Set.range v) = B.ker)
    (strain selfTensor target : T) :
    strain + (-2 : ℝ) • B.adjoint
        (normalCorrection B hB (target - strain - selfTensor)) + selfTensor - target =
      -inverseGramReconstruction v
        (frameContractions v (target - strain - selfTensor)) := by
  rw [completedTensor_error, ← hspan, starProjection_span_eq_inverseGramReconstruction hv]

omit [FiniteDimensional ℝ T] in
/-- `main:eq:mean-equation`: pointwise inverse-Gram transfer from reduced
error coordinates to the full tensor norm. -/
theorem norm_inverseGramReconstruction_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → T) (r : ι → ℝ) :
    ‖inverseGramReconstruction v r‖ ≤
      ∑ i, ∑ j, |(Matrix.gram ℝ v)⁻¹ i j| * |r j| * ‖v i‖ := by
  rw [inverseGramReconstruction_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, le_refl]

/-- `main:eq:mean-equation`: the norm of the full completed error is controlled
by the reduced defect coordinates and the inverse stress Gram matrix. -/
theorem completedTensor_error_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : T →ₗ[ℝ] V) (hB : Function.Surjective B) (v : ι → T)
    (hv : LinearIndependent ℝ v) (hspan : Submodule.span ℝ (Set.range v) = B.ker)
    (strain selfTensor target : T) :
    ‖strain + (-2 : ℝ) • B.adjoint
        (normalCorrection B hB (target - strain - selfTensor)) + selfTensor - target‖ ≤
      ∑ i, ∑ j, |(Matrix.gram ℝ v)⁻¹ i j| *
        |frameContractions v (target - strain - selfTensor) j| * ‖v i‖ := by
  rw [completedTensor_error_eq_inverseGram B hB v hv hspan, norm_neg]
  exact norm_inverseGramReconstruction_le v _

section Splitting

variable {U E : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup E] [Module ℝ E]

/-- `main:eq:mean-coarse-size`, `main:eq:mean-fine-size`: the coarse and fine
fields are an exact splitting of the same singly completed field. Here `J`
is the normal-completion map followed by ambient inclusion. No norm bounds
or geometric identities for `J` are assumed or asserted. -/
theorem completedField_eq_coarse_add_fine (L : U →ₗ[ℝ] E) (J : E →ₗ[ℝ] U)
    (coarse auxiliary : U) (target selfTensor coarseTensor : E) :
    coarse + auxiliary - (1 / 2 : ℝ) • J (target - L (coarse + auxiliary) - selfTensor) =
      (coarse + (1 / 2 : ℝ) • J (L coarse + coarseTensor)) +
        (auxiliary - (1 / 2 : ℝ) •
          J (target - L auxiliary - (selfTensor - coarseTensor))) := by
  simp only [map_add, map_sub, smul_add, smul_sub]
  abel

end Splitting

end JanetCartan.CurrentMean
