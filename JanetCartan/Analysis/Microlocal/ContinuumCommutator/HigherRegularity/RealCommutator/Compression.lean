module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Postcomposition
public import JanetCartan.Analysis.Operator.RealQuadratures

/-!
# Real compression of a continuous differential commutator

For `app:ch_background:eq:bg-commutator`, the actual real inclusion and real
part commute with smooth and weak ordered derivatives. Thus an actual complex
vector commutator gives the commutator of the literal `realOutputCompression`,
with the same additive estimate. The complex matrix producer must supply its
smooth identity and bound from primitive amplitude data; this transfer does not
assert those analytic inputs.
-/

@[expose] public noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
open PeriodicSobolevSpace
variable {n : ℕ} {I : Type*} [Fintype I]
local notation "Vℝ" => EuclideanSpace ℝ I
local notation "Vℂ" => EuclideanSpace ℂ I

/-- The concrete real commutator obtained by the existing real-part and
inclusion maps, for `app:ch_background:eq:bg-commutator`. -/
def compressedCommutator (s : ℕ)
    (K : PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ) :
    PeriodicSobolevSpace n Vℝ s →L[ℝ] PeriodicL2 n Vℝ :=
  l2RealPart volume ∘L K ∘L sobolevMap euclideanComplexInclusion s

/-- Real compression does not increase the additive one-high commutator
constant. The matrix producer supplies `hK` from its full-amplitude budgets
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_compressedCommutator_le (s : ℕ)
    (K : PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ u, ‖K u‖ ≤ C * (‖u‖ + B * ‖toL2 s u‖))
    (u : PeriodicSobolevSpace n Vℝ s) :
    ‖compressedCommutator s K u‖ ≤ C * (‖u‖ + B * ‖toL2 s u‖) := by
  have hi : ‖sobolevMap euclideanComplexInclusion s u‖ ≤ ‖u‖ :=
    (norm_sobolevMap_le _ _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (euclideanComplexInclusion_norm_le (ι := I)) (norm_nonneg u))
  have hi₂ : ‖toL2 s (sobolevMap euclideanComplexInclusion s u)‖ ≤ ‖toL2 s u‖ := by
    rw [toL2_sobolevMap]
    apply ((l2ComplexInclusion volume).le_opNorm (toL2 s u)).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (l2ComplexInclusion_norm_le (ι := I) (volume : Measure (Torus n))) (norm_nonneg _)
  calc
    _ ≤ ‖K (sobolevMap euclideanComplexInclusion s u)‖ := by
      change ‖l2RealPart volume (K (sobolevMap euclideanComplexInclusion s u))‖ ≤ _
      apply ((l2RealPart volume).le_opNorm _).trans
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (l2RealPart_norm_le (ι := I) (volume : Measure (Torus n))) (norm_nonneg _)
    _ ≤ C * (‖sobolevMap euclideanComplexInclusion s u‖ +
        B * ‖toL2 s (sobolevMap euclideanComplexInclusion s u)‖) := hK _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hi (mul_le_mul_of_nonneg_left hi₂ hB)) hC

/-- The exact smooth weak identity for the literal real compression. No
reality-preservation assumption on the complex PDO is used. Its complex smooth
identity is provided by the matrix commutator construction
(`app:ch_background:eq:bg-commutator`). -/
theorem compressedCommutator_ofSmooth (s : ℕ) (is : List (Fin n))
    (T : PeriodicL2 n Vℂ →L[ℂ] PeriodicL2 n Vℂ)
    (K : PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ)
    (hK : ∀ (f : Torus n → Vℂ) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList is (T (toL2 s (ofSmooth s f hf)))
        (T (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K (ofSmooth s f hf)))
    (f : Torus n → Vℝ) (hf : IsSmoothPeriodic f) :
    HasPeriodicWeakDerivativeList is
      (realOutputCompression T (toL2 s (ofSmooth s f hf)))
      (realOutputCompression T (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) + compressedCommutator s K (ofSmooth s f hf)) := by
  have h := weakDerivativeList_compLpL euclideanRealPart is
    (hK (fun x ↦ euclideanComplexInclusion (f x))
      (hf.comp_clm euclideanComplexInclusion))
  rw [← compLpL_ofSmooth euclideanComplexInclusion s s f hf,
    ← compLpL_derivative_ofSmooth euclideanComplexInclusion 0 0 is f hf,
    ← sobolevMap_ofSmooth euclideanComplexInclusion s f hf, map_add] at h
  exact h

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
