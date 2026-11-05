module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Literal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.IntegerBounds

/-!
# Natural-order tame estimates for the literal matrix PDO

For `app:ch_regular_base:eq:fio-input`, the scalar estimates are instantiated
from `IntegerBounds`, with the original Frobenius low and high budgets. There
is no assumed scalar or matrix estimate in the resulting statements. Smoothness,
physical support and the primitive coefficient budgets remain hypotheses for
consumers (graph normals, transport and continuum normal reduction) to supply.
The derivative shifts are independent of the natural Sobolev order.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- `app:ch_regular_base:eq:fio-input`: forward operator
preserves natural Sobolev order on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_matrixTwoPositionL2Operator_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : PiLp 2 (fun _ : J ↦ L²)), MemMatrixFourierSobolev (n : ℝ) f →
        let v := matrixTwoPositionL2Operator hd R b hb hs M
          (matrixAmplitude_entry_bound hM) f
        MemMatrixFourierSobolev (n : ℝ) v ∧
          matrixFourierSobolevNorm (n : ℝ) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (matrixFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hscalar⟩ :=
    exists_twoPositionL2Operator_integer_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  dsimp only
  unfold matrixTwoPositionL2Operator
  have hout := matrixOperator_fourierSobolev_bound
    (fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (matrixAmplitude_entry_bound hM i j))
    (n : ℝ) (n : ℝ) C (max 1 H) hC (by positivity)
    (fun i j g hg ↦ hscalar (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_entry_bound hM i j) (matrixAmplitude_entry_bound hH i j) g hg) f hf
  exact hout

/-- `app:ch_regular_base:eq:fio-input`: literal adjoint
preserves natural Sobolev order on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_matrixTwoPositionL2Operator_adjoint_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : PiLp 2 (fun _ : I ↦ L²)), MemMatrixFourierSobolev (n : ℝ) f →
        let v := (matrixTwoPositionL2Operator hd R b hb hs M
          (matrixAmplitude_entry_bound hM)).adjoint f
        MemMatrixFourierSobolev (n : ℝ) v ∧
          matrixFourierSobolevNorm (n : ℝ) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (matrixFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hscalar⟩ :=
    exists_twoPositionL2Operator_adjoint_integer_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  dsimp only
  unfold matrixTwoPositionL2Operator
  rw [matrixOperator_adjoint]
  have hout := matrixOperator_fourierSobolev_bound
    (fun j i ↦ (twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (matrixAmplitude_entry_bound hM i j)).adjoint)
    (n : ℝ) (n : ℝ) C (max 1 H) hC (by positivity)
    (fun j i g hg ↦ hscalar (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_entry_bound hM i j) (matrixAmplitude_entry_bound hH i j) g hg) f hf
  simpa only [mul_comm (Fintype.card J : ℝ) (Fintype.card I : ℝ)] using hout

/-- `app:ch_regular_base:eq:fio-input`: forward operator
gains one derivative on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_matrixTwoPositionL2Operator_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : PiLp 2 (fun _ : J ↦ L²)), MemMatrixFourierSobolev (n : ℝ) f →
        let v := matrixTwoPositionL2Operator hd R b hb hs M
          (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
            (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _)) f
        MemMatrixFourierSobolev ((n : ℝ) + 1) v ∧
          matrixFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (matrixFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hscalar⟩ :=
    exists_twoPositionL2Operator_integer_gain_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  dsimp only
  unfold matrixTwoPositionL2Operator
  have hout := matrixOperator_fourierSobolev_bound
    (fun i j ↦ twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
        (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _)))
    (n : ℝ) ((n : ℝ) + 1) C (max 1 H) hC (by positivity)
    (fun i j g hg ↦ hscalar (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_weighted_entry_bound hM i j) (matrixAmplitude_weighted_entry_bound hH i j) g hg) f hf
  exact hout

/-- `app:ch_regular_base:eq:fio-input`: literal adjoint
gains one derivative on all data. The constant is chosen before the amplitude and its
high budget. Matrix size contributes only the displayed fixed dimension factor. -/
theorem exists_matrixTwoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → P → Matrix I J ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (H : ℝ)
        (hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ H) →
        ∀ (f : PiLp 2 (fun _ : I ↦ L²)), MemMatrixFourierSobolev (n : ℝ) f →
        let v := (matrixTwoPositionL2Operator hd R b hb hs M
          (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
            (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _))).adjoint f
        MemMatrixFourierSobolev ((n : ℝ) + 1) v ∧
          matrixFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
              (matrixFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hscalar⟩ :=
    exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH f hf
  dsimp only
  unfold matrixTwoPositionL2Operator
  rw [matrixOperator_adjoint]
  have hout := matrixOperator_fourierSobolev_bound
    (fun j i ↦ (twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
        (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _))).adjoint)
    (n : ℝ) ((n : ℝ) + 1) C (max 1 H) hC (by positivity)
    (fun j i g hg ↦ hscalar (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_weighted_entry_bound hM i j) (matrixAmplitude_weighted_entry_bound hH i j) g hg) f hf
  simpa only [mul_comm (Fintype.card J : ℝ) (Fintype.card I : ℝ)] using hout

end JanetCartan.Pseudodifferential
