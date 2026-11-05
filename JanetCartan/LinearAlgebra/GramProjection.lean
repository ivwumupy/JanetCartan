module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Projection and reconstruction in a nonorthonormal frame

The Gram projection formula used in `main:eq:completion-error` of `paper.tex`.
A finite linearly independent family in a real inner-product space determines
an invertible Gram matrix. Its inverse reconstructs vectors in the span from
their contractions, and reconstructs the orthogonal projection of any vector.

`normalCompletion_error_eq_inverseGram` proves the algebraic error identity
with the manuscript's factors of `2` and `1 / 2`. To apply it to the geometric
normal completion, the frame must span the stress space, the inner product
must be the Frobenius contraction, and the tangent–normal identity must identify
the completed metric variation with the left-hand side. No geometric or
analytic identities are assumed or proved in this module.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open Matrix

namespace JanetCartan

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The frame contractions `q_F`, abstracting `main:eq:reduced-convention`. -/
def frameContractions (v : ι → E) (x : E) : ι → ℝ :=
  fun i ↦ ⟪v i, x⟫_ℝ

/-- Reconstruction from contractions by the inverse Gram matrix in
`main:eq:completion-error`. The projection properties require linear independence. -/
def inverseGramReconstruction (v : ι → E) (c : ι → ℝ) : E :=
  ∑ i, ((Matrix.gram ℝ v)⁻¹ *ᵥ c) i • v i

/-- The inverse-Gram sum lies in the frame span (`main:eq:completion-error`). -/
theorem inverseGramReconstruction_mem_span (v : ι → E) (c : ι → ℝ) :
    inverseGramReconstruction v c ∈ Submodule.span ℝ (Set.range v) := by
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The inverse-Gram sum has the prescribed contractions
(`main:eq:completion-error`). Linear independence supplies Gram invertibility. -/
theorem frameContractions_inverseGramReconstruction {v : ι → E}
    (hv : LinearIndependent ℝ v) (c : ι → ℝ) :
    frameContractions v (inverseGramReconstruction v c) = c := by
  have hdet : IsUnit (Matrix.gram ℝ v).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)
  have hm : Matrix.gram ℝ v *ᵥ ((Matrix.gram ℝ v)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  ext i
  simpa [frameContractions, inverseGramReconstruction, Matrix.mulVec, dotProduct,
    inner_sum, inner_smul_right, mul_comm] using congrFun hm i

/-- Subtracting the inverse-Gram reconstruction leaves a vector orthogonal
to the frame span (`main:eq:completion-error`). -/
theorem sub_inverseGramReconstruction_mem_orthogonal {v : ι → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    x - inverseGramReconstruction v (frameContractions v x) ∈
      (Submodule.span ℝ (Set.range v))ᗮ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (congrFun (frameContractions_inverseGramReconstruction hv
      (frameContractions v x)) i).symm
  | zero => simp
  | add a b ha hb ha' hb' => simp [inner_add_left, ha', hb']
  | smul a y hy hy' => simp [inner_smul_left, hy']

/-- The finite frame span in `main:eq:completion-error` is finite dimensional,
so projection exists without a completeness assumption on the ambient space. -/
local instance frameSpanFiniteDimensional (v : ι → E) :
    FiniteDimensional ℝ (Submodule.span ℝ (Set.range v)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range v)

/-- The inverse-Gram reconstruction of contractions is the orthogonal
projection onto the frame span (`main:eq:completion-error`). -/
theorem starProjection_span_eq_inverseGramReconstruction {v : ι → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    (Submodule.span ℝ (Set.range v)).starProjection x =
      inverseGramReconstruction v (frameContractions v x) := by
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (inverseGramReconstruction_mem_span _ _)
    (sub_inverseGramReconstruction_mem_orthogonal hv x)

/-- The expanded double sum appearing in `main:eq:completion-error`. -/
theorem inverseGramReconstruction_eq_sum (v : ι → E) (c : ι → ℝ) :
    inverseGramReconstruction v c =
      ∑ i, ∑ j, ((Matrix.gram ℝ v)⁻¹ i j * c j) • v i := by
  simp only [inverseGramReconstruction, Matrix.mulVec, dotProduct, Finset.sum_smul]

/-- The inverse-Gram formula for orthogonal projection, in the explicit
double-sum form used in `main:eq:completion-error`. -/
theorem orthogonalProjectionOnto_span_eq_sum {v : ι → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    ((Submodule.span ℝ (Set.range v)).orthogonalProjectionOnto x : E) =
      ∑ i, ∑ j, ((Matrix.gram ℝ v)⁻¹ i j * ⟪v j, x⟫_ℝ) • v i := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply,
    starProjection_span_eq_inverseGramReconstruction hv, inverseGramReconstruction_eq_sum]
  rfl

/-- A vector in the frame span is reconstructed from its contractions
(`main:eq:completion-error`). -/
theorem inverseGramReconstruction_frameContractions {v : ι → E}
    (hv : LinearIndependent ℝ v) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    inverseGramReconstruction v (frameContractions v x) = x := by
  rw [← starProjection_span_eq_inverseGramReconstruction hv]
  exact Submodule.starProjection_eq_self_iff.mpr hx

/-- Explicit reconstruction of a vector in the frame span
(`main:eq:completion-error`). -/
theorem eq_sum_inverseGram_of_mem_span {v : ι → E}
    (hv : LinearIndependent ℝ v) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    x = ∑ i, ∑ j, ((Matrix.gram ℝ v)⁻¹ i j * ⟪v j, x⟫_ℝ) • v i := by
  rw [← inverseGramReconstruction_eq_sum]
  exact (inverseGramReconstruction_frameContractions hv hx).symm

/-- Contractions uniquely determine a vector in the frame span
(`main:eq:completion-error`). -/
theorem frameContractions_injOn_span {v : ι → E}
    (hv : LinearIndependent ℝ v) :
    Set.InjOn (frameContractions v) (Submodule.span ℝ (Set.range v)) := by
  intro x hx y hy hxy
  rw [← inverseGramReconstruction_frameContractions hv hx,
    ← inverseGramReconstruction_frameContractions hv hy, hxy]

/-- The reconstructed error vanishes exactly when its contraction data vanish
(`main:eq:completion-error`). -/
theorem inverseGramReconstruction_eq_zero_iff {v : ι → E}
    (hv : LinearIndependent ℝ v) (c : ι → ℝ) :
    inverseGramReconstruction v c = 0 ↔ c = 0 := by
  constructor
  · intro h
    rw [← frameContractions_inverseGramReconstruction hv c, h]
    ext i
    simp [frameContractions]
  · rintro rfl
    simp [inverseGramReconstruction]

/-- The algebraic full-error identity of `main:eq:completion-error`. Here `a`
represents the symmetrized covariant derivative and the complementary projection
represents the normal correction from `main:eq:normal-completion`. -/
theorem normalCompletion_error_eq_inverseGram {v : ι → E}
    (hv : LinearIndependent ℝ v) (a h : E) :
    (2 : ℝ) • a - (2 : ℝ) • (Submodule.span ℝ (Set.range v))ᗮ.starProjection
        (a - (1 / 2 : ℝ) • h) - h =
      (2 : ℝ) • ∑ i, ∑ j, ((Matrix.gram ℝ v)⁻¹ i j *
        (⟪v j, a⟫_ℝ - (1 / 2 : ℝ) * ⟪v j, h⟫_ℝ)) • v i := by
  calc
    _ = (2 : ℝ) • (Submodule.span ℝ (Set.range v)).starProjection
        (a - (1 / 2 : ℝ) • h) := by
      rw [Submodule.starProjection_orthogonal_val]
      simp only [smul_sub, smul_smul]
      norm_num
      abel
    _ = _ := by
      rw [starProjection_span_eq_inverseGramReconstruction hv, inverseGramReconstruction_eq_sum]
      simp only [frameContractions, inner_sub_right, inner_smul_right]

/-- The algebraic normal completion solves the full equation exactly when the
reduced equations, with their factor `1 / 2`, hold (`main:eq:reduced-equation`
and `main:eq:completion-error`). -/
theorem normalCompletion_eq_iff_frameContractions {v : ι → E}
    (hv : LinearIndependent ℝ v) (a h : E) :
    (2 : ℝ) • a - (2 : ℝ) • (Submodule.span ℝ (Set.range v))ᗮ.starProjection
        (a - (1 / 2 : ℝ) • h) = h ↔
      ∀ j, ⟪v j, a⟫_ℝ = (1 / 2 : ℝ) * ⟪v j, h⟫_ℝ := by
  rw [← sub_eq_zero, normalCompletion_error_eq_inverseGram hv,
    ← inverseGramReconstruction_eq_sum]
  simp only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    inverseGramReconstruction_eq_zero_iff hv, funext_iff, Pi.zero_apply, sub_eq_zero]

end JanetCartan
