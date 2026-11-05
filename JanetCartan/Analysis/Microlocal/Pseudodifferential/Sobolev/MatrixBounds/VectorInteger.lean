module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Integer
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# All-data integer estimates on literal vector L²

The vector form of `app:ch_regular_base:eq:fio-input`, with scalar estimates
already discharged by `IntegerBounds` and exact coordinate isometries. Geometric
consumers must supply the primitive smoothness, support and Frobenius budgets.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))

/-- The actual vector-valued two-position PDO for
`app:ch_regular_base:thm:actual-calculus`. -/
def vectorTwoPositionL2Operator (hd : 0 < d) (R : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (M : ℝ)
    (hM : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) M) :
    Lp (EuclideanSpace ℂ J) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) :=
  vectorMatrixL2Operator (fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
    ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hM i j))

/-- `app:ch_regular_base:eq:fio-input`: forward operator
preserves natural Sobolev order on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_vectorTwoPositionL2Operator_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := vectorTwoPositionL2Operator hd R b hb hs M
          (matrixAmplitude_entry_bound hM) f
        MemVectorFourierSobolev (n : ℝ) v ∧
          vectorFourierSobolevNorm (n : ℝ) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hm⟩ := exists_matrixTwoPositionL2Operator_integer_tame_constant_all_data (I := I) (J := J) hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  have h := hm b hb hs H hM hH (finiteL2CoordinateIsometry volume f) hf
  simpa only [MemVectorFourierSobolev, vectorFourierSobolevNorm,
    vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixTwoPositionL2Operator,
    matrixOperator_adjoint, LinearIsometryEquiv.norm_map] using h

/-- `app:ch_regular_base:eq:fio-input`: literal adjoint
preserves natural Sobolev order on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_vectorTwoPositionL2Operator_adjoint_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (vectorTwoPositionL2Operator hd R b hb hs M
          (matrixAmplitude_entry_bound hM)).adjoint f
        MemVectorFourierSobolev (n : ℝ) v ∧
          vectorFourierSobolevNorm (n : ℝ) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hm⟩ := exists_matrixTwoPositionL2Operator_adjoint_integer_tame_constant_all_data (I := I) (J := J) hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  have h := hm b hb hs H hM hH (finiteL2CoordinateIsometry volume f) hf
  simpa only [MemVectorFourierSobolev, vectorFourierSobolevNorm,
    vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixTwoPositionL2Operator,
    matrixOperator_adjoint, LinearIsometryEquiv.norm_map] using h

/-- `app:ch_regular_base:eq:fio-input`: forward operator
gains one derivative on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_vectorTwoPositionL2Operator_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := vectorTwoPositionL2Operator hd R b hb hs M
          (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
            (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _)) f
        MemVectorFourierSobolev ((n : ℝ) + 1) v ∧
          vectorFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hm⟩ := exists_matrixTwoPositionL2Operator_integer_gain_tame_constant_all_data (I := I) (J := J) hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  have h := hm b hb hs H hM hH (finiteL2CoordinateIsometry volume f) hf
  simpa only [MemVectorFourierSobolev, vectorFourierSobolevNorm,
    vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixTwoPositionL2Operator,
    matrixOperator_adjoint, LinearIsometryEquiv.norm_map] using h

/-- `app:ch_regular_base:eq:fio-input`: literal adjoint
gains one derivative on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_vectorTwoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (vectorTwoPositionL2Operator hd R b hb hs M
          (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
            (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _))).adjoint f
        MemVectorFourierSobolev ((n : ℝ) + 1) v ∧
          vectorFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hm⟩ := exists_matrixTwoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data (I := I) (J := J) hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  have h := hm b hb hs H hM hH (finiteL2CoordinateIsometry volume f) hf
  simpa only [MemVectorFourierSobolev, vectorFourierSobolevNorm,
    vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixTwoPositionL2Operator,
    matrixOperator_adjoint, LinearIsometryEquiv.norm_map] using h

end JanetCartan.Pseudodifferential
