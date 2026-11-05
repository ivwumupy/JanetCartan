module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.Normalization

/-!
# Integer estimates for the same physical canonical PDO

The operator identification transfers the existing vector matrix estimates
without changing either mask, the finite Hilbert norm or Frobenius budgets.
Consumer: the four `CompleteResidual.directPDOSymbols` in
`app:ch_regular_base:eq:energy-complete-residual`, followed by
`FixedDomainInverse.LocalL2`. The sector amplitude producer must still supply
the displayed primitive budgets for those literal symbols.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.PdoRealization
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential AmplitudeBound
variable {d r : ℕ}
local notation "E" => Euclidean d
local notation "P" => Euclidean (2 * d)

/-- Forward natural-order estimate for the actual canonical graph PDO in
`app:ch_regular_base:eq:fio-input`. The low reserve is `2 * (d + 1)`,
independent of Sobolev order; the high term is a single Frobenius quantity.
Consumer: `CompleteResidual.directPDOSymbols` and `FixedDomainInverse.LocalL2`. -/
theorem exists_canonicalGraph_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A) f
        MemVectorFourierSobolev (n : ℝ) v ∧
          vectorFourierSobolevNorm (n : ℝ) v ≤
            ((r : ℝ) * r * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_vectorTwoPositionL2Operator_integer_tame_constant_all_data
    (I := Fin r) (J := Fin r) hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f hf
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M
    (matrixAmplitude_entry_bound hM)
  simpa only [he, Fintype.card_fin] using
    hbound (physicalPDOCycleSymbol A) hb hs H hM hH f hf

/-- Forward gain-one estimate for the actual canonical graph PDO in
`app:ch_regular_base:eq:fio-input`. The low reserve is `2 * (d + 1) + 1`,
independent of Sobolev order; the high term is a single Frobenius quantity.
Consumer: `CompleteResidual.directPDOSymbols` and `FixedDomainInverse.LocalL2`. -/
theorem exists_canonicalGraph_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A) f
        MemVectorFourierSobolev ((n : ℝ) + 1) v ∧
          vectorFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((r : ℝ) * r * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_vectorTwoPositionL2Operator_integer_gain_tame_constant_all_data
    (I := Fin r) (J := Fin r) hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f hf
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M
    (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
      (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _))
  simpa only [he, Fintype.card_fin] using
    hbound (physicalPDOCycleSymbol A) hb hs H hM hH f hf

/-- Literal-adjoint natural-order estimate for the actual canonical graph PDO in
`app:ch_regular_base:eq:fio-input`. The low reserve is `2 * (d + 1)`,
independent of Sobolev order; the high term is a single Frobenius quantity.
Consumer: `CompleteResidual.directPDOSymbols` and `FixedDomainInverse.LocalL2`. -/
theorem exists_canonicalGraph_adjoint_integer_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + n → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A).adjoint f
        MemVectorFourierSobolev (n : ℝ) v ∧
          vectorFourierSobolevNorm (n : ℝ) v ≤
            ((r : ℝ) * r * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_vectorTwoPositionL2Operator_adjoint_integer_tame_constant_all_data
    (I := Fin r) (J := Fin r) hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f hf
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M
    (matrixAmplitude_entry_bound hM)
  simpa only [he, Fintype.card_fin] using
    hbound (physicalPDOCycleSymbol A) hb hs H hM hH f hf

/-- Literal-adjoint gain-one estimate for the actual canonical graph PDO in
`app:ch_regular_base:eq:fio-input`. The low reserve is `2 * (d + 1) + 1`,
independent of Sobolev order; the high term is a single Frobenius quantity.
Consumer: `CompleteResidual.directPDOSymbols` and `FixedDomainInverse.LocalL2`. -/
theorem exists_canonicalGraph_adjoint_integer_gain_tame_constant_all_data
    (hd : 0 < d) (R : ℝ) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : FullAmplitude d r) (_hb : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol A)))
        (_hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ physicalPDOCycleSymbol A ξ z i j)) (H : ℝ)
        (_hM : ∀ ξ is, is.length ≤ 2 * (d + 1) + 1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ M),
        (∀ ξ is, is.length ≤ 2 * (d + 1) + (n + 1) → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol A ξ) z‖ ≤ H) →
        ∀ (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)), MemVectorFourierSobolev (n : ℝ) f →
        let v := (fullGraphOperator (fun x η ↦ inner ℝ x η) A).adjoint f
        MemVectorFourierSobolev ((n : ℝ) + 1) v ∧
          vectorFourierSobolevNorm ((n : ℝ) + 1) v ≤
            ((r : ℝ) * r * C) *
              (vectorFourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_vectorTwoPositionL2Operator_adjoint_integer_gain_tame_constant_all_data
    (I := Fin r) (J := Fin r) hd R n M
  refine ⟨C, hC, ?_⟩
  intro A hb hs H hM hH f hf
  have he := canonicalGraph_eq_vectorTwoPositionL2Operator hd R A hb hs M
    (fun i j ↦ amplitudeDerivativeBound_of_le (amplitudeDerivativeBound_of_weighted
      (matrixAmplitude_weighted_entry_bound hM i j)) (Nat.le_succ _))
  simpa only [he, Fintype.card_fin] using
    hbound (physicalPDOCycleSymbol A) hb hs H hM hH f hf

end JanetCartan.RegularSector.Characteristic.PdoRealization
