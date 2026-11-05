module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.IntegerBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Duality

/-!
# Negative integer estimates for the same canonical PDO

Positive estimates for the literal scalar adjoints, Euclidean weighted
Fourier duality, and the existing finite Hilbert matrix lifting give the
negative integer bounds in `app:ch_regular_base:eq:negative-duality`.
The gain-one estimate maps `H^(-k-1)` to `H^(-k)`. Every estimate is for
the SAME canonical graph operator on actual vector L² data; its negative
Sobolev norm is the original weighted Euclidean Fourier norm.

The constants precede the amplitude and high budget. The low derivative
reserves are unchanged, and the single high symbol quantity occurs linearly.
The sector parent must instantiate these primitive budgets for its actual
four masked direct symbols. Consumer: the negative-duality step for the
complete residual and its literal adjoint in `FixedDomainInverse.LocalL2`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential AmplitudeBound
variable {d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean (2 * d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- Forward negative integer order-zero estimate,
with a fixed derivative reserve and one high symbol quantity. The bound is
proved from the opposite positive estimate, including `k = 0`, as required
by `app:ch_regular_base:eq:negative-duality`. -/
theorem exists_canonicalGraph_negative_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)),
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A) f
        MemVectorFourierSobolev (-(n : ℝ)) v ∧
          vectorFourierSobolevNorm (-(n : ℝ)) v ≤
            ((r : ℝ) * r * C) *
              (1 + max 1 H) * vectorFourierSobolevNorm (-(n : ℝ)) f := by
  obtain ⟨C, hC, hpos⟩ := exists_twoPositionL2Operator_adjoint_integer_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f
  let b := physicalPDOCycleSymbol A
  let hbase := matrixAmplitude_entry_bound hM
  let T : Fin r → Fin r → L² →L[ℂ] L² := fun i j ↦
    twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hbase i j)
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M hbase
  have hentry (i j : Fin r) (g : L²) (_hg : MemFourierSobolev (-(n : ℝ)) g) :
      MemFourierSobolev (-(n : ℝ)) (T i j g) ∧
        fourierSobolevNorm (-(n : ℝ)) (T i j g) ≤
          (C * (1 + max 1 H)) * (fourierSobolevNorm (-(n : ℝ)) g + 0 * ‖g‖) := by
    have hp := hpos (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_entry_bound hM i j) (matrixAmplitude_entry_bound hH i j)
    have hdual := negativeFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg n)
      (Nat.cast_nonneg n) hC (show 0 ≤ max 1 H by positivity) (T i j)
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp v hv) g
    simpa only [zero_mul, add_zero] using hdual
  have hf : MemVectorFourierSobolev (-(n : ℝ)) f :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg n)) _
  have hv := vectorMatrixL2Operator_fourierSobolev_bound T
    (-(n : ℝ)) (-(n : ℝ)) (C * (1 + max 1 H)) 0 (by positivity) le_rfl hentry f hf
  simpa only [he, vectorTwoPositionL2Operator,
    Fintype.card_fin, zero_mul, add_zero, mul_assoc] using hv

/-- Forward negative integer gain-one estimate,
with a fixed derivative reserve and one high symbol quantity. The bound is
proved from the opposite positive estimate, including `k = 0`, as required
by `app:ch_regular_base:eq:negative-duality`. -/
theorem exists_canonicalGraph_negative_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)),
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A) f
        MemVectorFourierSobolev (-(n : ℝ)) v ∧
          vectorFourierSobolevNorm (-(n : ℝ)) v ≤
            ((r : ℝ) * r * C) *
              (1 + max 1 H) * vectorFourierSobolevNorm (-((n : ℝ) + 1)) f := by
  obtain ⟨C, hC, hpos⟩ := exists_twoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f
  let b := physicalPDOCycleSymbol A
  let hbase := fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
      (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _)
  let T : Fin r → Fin r → L² →L[ℂ] L² := fun i j ↦
    twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hbase i j)
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M hbase
  have hentry (i j : Fin r) (g : L²) (_hg : MemFourierSobolev (-((n : ℝ) + 1)) g) :
      MemFourierSobolev (-(n : ℝ)) (T i j g) ∧
        fourierSobolevNorm (-(n : ℝ)) (T i j g) ≤
          (C * (1 + max 1 H)) * (fourierSobolevNorm (-((n : ℝ) + 1)) g + 0 * ‖g‖) := by
    have hp := hpos (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) H
      (matrixAmplitude_weighted_entry_bound hM i j) (matrixAmplitude_weighted_entry_bound hH i j)
    have hdual := negativeFourierSobolev_tame_bound_of_adjoint (t := (n : ℝ) + 1) (Nat.cast_nonneg n)
      (by positivity) hC (show 0 ≤ max 1 H by positivity) (T i j)
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp v hv) g
    simpa only [zero_mul, add_zero] using hdual
  have hf : MemVectorFourierSobolev (-((n : ℝ) + 1)) f :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr (show 0 ≤ (n : ℝ) + 1 by positivity)) _
  have hv := vectorMatrixL2Operator_fourierSobolev_bound T
    (-((n : ℝ) + 1)) (-(n : ℝ)) (C * (1 + max 1 H)) 0 (by positivity) le_rfl hentry f hf
  simpa only [he, vectorTwoPositionL2Operator,
    Fintype.card_fin, zero_mul, add_zero, mul_assoc] using hv

/-- Literal-adjoint negative integer order-zero estimate,
with a fixed derivative reserve and one high symbol quantity. The bound is
proved from the opposite positive estimate, including `k = 0`, as required
by `app:ch_regular_base:eq:negative-duality`. -/
theorem exists_canonicalGraph_adjoint_negative_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)),
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A).adjoint f
        MemVectorFourierSobolev (-(n : ℝ)) v ∧
          vectorFourierSobolevNorm (-(n : ℝ)) v ≤
            ((r : ℝ) * r * C) *
              (1 + max 1 H) * vectorFourierSobolevNorm (-(n : ℝ)) f := by
  obtain ⟨C, hC, hpos⟩ := exists_twoPositionL2Operator_integer_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f
  let b := physicalPDOCycleSymbol A
  let hbase := matrixAmplitude_entry_bound hM
  let T : Fin r → Fin r → L² →L[ℂ] L² := fun i j ↦
    twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hbase i j)
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M hbase
  have hentry (i j : Fin r) (g : L²) (_hg : MemFourierSobolev (-(n : ℝ)) g) :
      MemFourierSobolev (-(n : ℝ)) ((T j i).adjoint g) ∧
        fourierSobolevNorm (-(n : ℝ)) ((T j i).adjoint g) ≤
          (C * (1 + max 1 H)) * (fourierSobolevNorm (-(n : ℝ)) g + 0 * ‖g‖) := by
    have hp := hpos (fun ξ z ↦ b ξ z j i)
      ((matrixEntryEvaluation j i).contDiff.comp hb) (fun ξ ↦ hs ξ j i) H
      (matrixAmplitude_entry_bound hM j i) (matrixAmplitude_entry_bound hH j i)
    have hdual := negativeFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg n)
      (Nat.cast_nonneg n) hC (show 0 ≤ max 1 H by positivity) ((T j i).adjoint)
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp v hv) g
    simpa only [zero_mul, add_zero] using hdual
  have hf : MemVectorFourierSobolev (-(n : ℝ)) f :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg n)) _
  have hv := vectorMatrixL2Operator_fourierSobolev_bound (fun i j ↦ (T j i).adjoint)
    (-(n : ℝ)) (-(n : ℝ)) (C * (1 + max 1 H)) 0 (by positivity) le_rfl hentry f hf
  simpa only [he, vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    Fintype.card_fin, zero_mul, add_zero, mul_assoc] using hv

/-- Literal-adjoint negative integer gain-one estimate,
with a fixed derivative reserve and one high symbol quantity. The bound is
proved from the opposite positive estimate, including `k = 0`, as required
by `app:ch_regular_base:eq:negative-duality`. -/
theorem exists_canonicalGraph_adjoint_negative_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)),
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A).adjoint f
        MemVectorFourierSobolev (-(n : ℝ)) v ∧
          vectorFourierSobolevNorm (-(n : ℝ)) v ≤
            ((r : ℝ) * r * C) *
              (1 + max 1 H) * vectorFourierSobolevNorm (-((n : ℝ) + 1)) f := by
  obtain ⟨C, hC, hpos⟩ := exists_twoPositionL2Operator_integer_gain_tame_constant_all_data hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f
  let b := physicalPDOCycleSymbol A
  let hbase := fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
      (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _)
  let T : Fin r → Fin r → L² →L[ℂ] L² := fun i j ↦
    twoPositionL2Operator hd R (fun ξ z ↦ b ξ z i j)
      ((matrixEntryEvaluation i j).contDiff.comp hb) (fun ξ ↦ hs ξ i j) M (hbase i j)
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M hbase
  have hentry (i j : Fin r) (g : L²) (_hg : MemFourierSobolev (-((n : ℝ) + 1)) g) :
      MemFourierSobolev (-(n : ℝ)) ((T j i).adjoint g) ∧
        fourierSobolevNorm (-(n : ℝ)) ((T j i).adjoint g) ≤
          (C * (1 + max 1 H)) * (fourierSobolevNorm (-((n : ℝ) + 1)) g + 0 * ‖g‖) := by
    have hp := hpos (fun ξ z ↦ b ξ z j i)
      ((matrixEntryEvaluation j i).contDiff.comp hb) (fun ξ ↦ hs ξ j i) H
      (matrixAmplitude_weighted_entry_bound hM j i) (matrixAmplitude_weighted_entry_bound hH j i)
    have hdual := negativeFourierSobolev_tame_bound_of_adjoint (t := (n : ℝ) + 1) (Nat.cast_nonneg n)
      (by positivity) hC (show 0 ≤ max 1 H by positivity) ((T j i).adjoint)
      (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp v hv) g
    simpa only [zero_mul, add_zero] using hdual
  have hf : MemVectorFourierSobolev (-((n : ℝ) + 1)) f :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr (show 0 ≤ (n : ℝ) + 1 by positivity)) _
  have hv := vectorMatrixL2Operator_fourierSobolev_bound (fun i j ↦ (T j i).adjoint)
    (-((n : ℝ) + 1)) (-(n : ℝ)) (C * (1 + max 1 H)) 0 (by positivity) le_rfl hentry f hf
  simpa only [he, vectorTwoPositionL2Operator, vectorMatrixL2Operator_adjoint,
    Fintype.card_fin, zero_mul, add_zero, mul_assoc] using hv

end JanetCartan.RegularSector.Characteristic.PdoRealization
