module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel

/-!
# Fixed contractions of the joint phase Hessian

For `app:ch_response:eq:direct-envelope-profile`, the mixed matrix and the
covector Hessian are fixed linear contractions. These maps supply the
phase-jet extraction consumed by the averaged mixed inverse and the parameter
coefficient. The mixed matrix has its Frobenius norm throughout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance phaseJetMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Fixed extraction of `S_{xξ}` from the joint Hessian, in the order used by
`FourierIntegral.mixedPhaseMatrix` (`app:ch_response:eq:direct-envelope-profile`). -/
def mixedHessianContraction (n : ℕ) :
    ((Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ) →L[ℝ]
      Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
    (F' := Matrix (Fin n) (Fin n) ℝ) {
    toFun := fun H i j ↦ H (0, EuclideanSpace.single j 1) (EuclideanSpace.single i 1, 0)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The literal entries of the fixed mixed extraction
(`app:ch_response:eq:direct-envelope-profile`). -/
@[simp] theorem mixedHessianContraction_apply {n : ℕ}
    (H : (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
    (i j : Fin n) :
    mixedHessianContraction n H i j =
      H (0, EuclideanSpace.single j 1) (EuclideanSpace.single i 1, 0) := rfl

/-- The fixed Frobenius conversion costs at most the dimension, including
in dimension zero (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_mixedHessianContraction_apply_le {n : ℕ}
    (H : (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ) :
    ‖mixedHessianContraction n H‖ ≤ (n : ℝ) * ‖H‖ := by
  have he (i j : Fin n) : ‖mixedHessianContraction n H i j‖ ≤ ‖H‖ := by
    have h := (H.le_opNorm₂ (0, EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1, 0))
    simpa using h
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Nat.cast_nonneg n) (norm_nonneg H), ?_⟩
  simp only [Real.rpow_two]
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖H‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (he i j) 2
    _ = _ := by simp; ring

/-- Fixed restriction of both Hessian slots to covectors, for the parameter
coefficient in `app:ch_response:eq:direct-envelope-profile`. -/
def covectorHessianContraction (n : ℕ) :
    ((Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ) →L[ℝ]
      Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
    (F' := Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ) {
    toFun := fun H ↦
      ((ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n × Euclidean n) ℝ).flip
        (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n))).comp
          (H.comp (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n)))
    map_add' := by intros; ext; rfl
    map_smul' := by intros; ext; rfl }

/-- Evaluation of the covector restriction
(`app:ch_response:eq:direct-envelope-profile`). -/
@[simp] theorem covectorHessianContraction_apply {n : ℕ}
    (H : (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ)
    (v w : Euclidean n) :
    covectorHessianContraction n H v w = H (0, v) (0, w) := rfl

/-- Restricting the two covector slots costs no norm factor
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_covectorHessianContraction_apply_le {n : ℕ}
    (H : (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) →L[ℝ] ℝ) :
    ‖covectorHessianContraction n H‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg H) (norm_nonneg v))
  intro w
  simpa using H.le_opNorm₂ (0, v) (0, w)

end JanetCartan.ResponseTransfer.GradedPrimitives
