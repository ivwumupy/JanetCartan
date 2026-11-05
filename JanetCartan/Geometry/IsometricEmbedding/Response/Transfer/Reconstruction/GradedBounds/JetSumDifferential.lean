module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.PhysicalExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.GradedBounds.EnvelopeDerivatives

/-! # Differentiating the literal finite jet sum

Product rule used to identify the L² physical derivative in
`app:ch_response:eq:response-graded-derivative`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
open JanetCartan.AmplitudeBound
namespace JanetCartan.IsometricEmbedding.Reconstruction
variable {d : ℕ} {J : Type*} [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Product differentiation of an actual finite classical jet sum, for
`app:ch_response:eq:response-reconstruction-grading`. -/
theorem reconstructionJetSum_differential (c f : J → E → ℂ) (q : J → ℂ)
    (w : J → List (Fin d)) {x : E}
    (hc : ∀ j, DifferentiableAt ℝ (c j) x) (hf : ∀ j, ContDiff ℝ ∞ (f j)) :
    DifferentiableAt ℝ (fun y ↦ ∑ j, q j * (c j y * euclideanCoordinateDerivList (w j) (f j) y)) x ∧
      ∀ i, fderiv ℝ (fun y ↦ ∑ j, q j * (c j y * euclideanCoordinateDerivList (w j) (f j) y))
        x (EuclideanSpace.single i 1) =
        ∑ j, q j * (fderiv ℝ (c j) x (EuclideanSpace.single i 1) *
          euclideanCoordinateDerivList (w j) (f j) x +
          c j x * euclideanCoordinateDerivList (i :: w j) (f j) x) := by
  have hd j := (contDiff_euclideanCoordinateDerivList (hf j) (w j)).differentiable (by simp) x
  have ht j := ((hc j).mul (hd j)).const_mul (q j)
  refine ⟨DifferentiableAt.fun_sum (fun j _ ↦ ht j), fun i ↦ ?_⟩
  erw [fderiv_fun_sum (u := Finset.univ) (fun j _ ↦ ht j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_const_mul ((hc j).mul (hd j))]
  have he := ((hc j).hasFDerivAt.mul (hd j).hasFDerivAt).fderiv
  rw [he]
  simp only [smul_apply, add_apply, smul_eq_mul, euclideanCoordinateDerivList]
  ring

end JanetCartan.IsometricEmbedding.Reconstruction
