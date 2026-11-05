module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.Leibniz

/-!
# Actual image multipliers and their allocated Sobolev bounds

For `app:ch_background:eq:bg-commutator` and `app:ch_background:prop:bg-inverse`,
this module constructs the Sobolev actions of the existing scalar and matrix
coefficient multipliers, proves their full Leibniz identities and retains the
complementary coefficient/datum derivative orders. The consumer is the higher
commutator of the same image normal; no multiplier estimate is assumed.
-/

public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace

variable {n : ℕ}

/-- Differentiated scalar coefficients are controlled by jets of the original
coefficient through exactly `j + js.length`, with datum order `s-j`
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_cutoffSobolev_orderedCoefficient_le (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (js : List (Fin n)) (s : ℕ)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖cutoffSobolev (orderedCoefficient q hq js) (hq.coordinateDerivList js) s u‖ ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1),
          ((j + 1) * cNorm (fundamentalCell n) (j + js.length) (periodicLift q)) *
            (periodicSobolevScale n (Euclidean n)).gradeNorm (s-j) (toL2 s u) := by
  apply (norm_cutoffSobolev_le_gradeNorm _ (hq.coordinateDerivList js) s u).trans
  apply mul_le_mul_of_nonneg_left _ (AuxiliaryRawBand.coefficientProductConstant_nonneg n s)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (cNorm_periodicCoordinateDerivList_le q hq js j)
    ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg _ _)

/-- The same allocated estimate for the actual reduced matrix coefficient,
including every principal and connection coefficient in the image normal
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_reducedCoefficientSobolev_orderedCoefficient_le (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) (js : List (Fin n)) (s : ℕ) (i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖reducedCoefficientSobolev (orderedCoefficient q hq js) (hq.coordinateDerivList js) s i k u‖ ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1),
          ((j + 1) * cNorm (fundamentalCell n) (j + js.length) (periodicLift q)) *
            (periodicSobolevScale n (Euclidean n)).gradeNorm (s-j) (toL2 s u) :=
  (norm_matrixUnitSobolev_le s i k _).trans
    (norm_cutoffSobolev_orderedCoefficient_le q hq js s u)

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
