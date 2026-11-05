module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorFirstDerivative

/-!
# Coordinate derivatives retain vector Fourier regularity

The successor step for the natural-order restriction comparison in
`app:not:fourier`. Each derivative is an actual vector L² class. Its lower-order
Fourier membership follows from the scalar derivative characterization; the
finite fiber factor is explicit and no derivative is lost.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

open Pseudodifferential

variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Coordinate derivatives of vector H^(s+1) data have actual vector H^s
representatives and a genuine first weak derivative identity. This supplies
the induction input for the restriction norm comparison of `app:not:fourier`. -/
theorem exists_vector_coordinateDerivatives_norm_bounds {s : ℝ} (hs : 0 ≤ s)
    (u : Lp F 2 (volume : Measure E)) (hu : MemVectorFourierSobolev (s + 1) u) :
    ∃ v : Fin n → Lp F 2 (volume : Measure E),
      (∀ i, MemVectorFourierSobolev s (v i)) ∧
      Mollification.HasWeakFDerivOn volume u (coordinateFDeriv (fun i ↦ v i)) univ ∧
      ‖u‖ + (∑ i, vectorFourierSobolevNorm s (v i)) ≤
        (((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) * vectorFourierSobolevNorm (s + 1) u := by
  choose hbase w hw hn₁ hn₂ using fun a ↦
    (hu a).exists_coordinateDerivatives_norm_bounds hs
  let v (i : Fin n) : Lp F 2 (volume : Measure E) :=
    (finiteL2CoordinateIsometry volume).symm (WithLp.toLp 2 (fun a ↦ w a i))
  have hv (i : Fin n) (a : Fin r) : finiteL2CoordinateIsometry volume (v i) a = w a i := by
    simp [v]
  have htest := fun ψ hψ hc i ↦ vector_integral_test_of_coordinateDerivatives u (v i) i
    (fun a ↦ by rw [hv]; exact (hw a i).1) ψ hψ hc
  refine ⟨v, fun i a ↦ ?_,
    hasWeakFDerivOn_coordinateFDeriv (Lp.memLp u) (fun i ↦ Lp.memLp (v i)) htest, ?_⟩
  · change MemFourierSobolev s (finiteL2CoordinateIsometry volume (v i) a)
    rw [hv]
    exact (hw a i).2
  have hvnorm (i : Fin n) : vectorFourierSobolevNorm s (v i) ≤
      ∑ a, fourierSobolevNorm s (w a i) := by
    simpa only [vectorFourierSobolevNorm, v, LinearIsometryEquiv.apply_symm_apply,
      PiLp.toLp_apply] using matrixFourierSobolevNorm_le_sum (d := n) s
        (WithLp.toLp 2 (fun a ↦ w a i))
  have hunorm : ‖u‖ ≤ ∑ a, fourierSobolevNorm s (finiteL2CoordinateIsometry volume u a) := by
    calc
      _ ≤ ∑ a, ‖finiteL2CoordinateIsometry volume u a‖ := by
        simpa using matrixFourierSobolevNorm_le_sum (d := n) 0 (finiteL2CoordinateIsometry volume u)
      _ ≤ _ := Finset.sum_le_sum fun a _ ↦ norm_le_fourierSobolevNorm hs (hbase a)
  have hnonneg : 0 ≤ vectorFourierSobolevNorm (s + 1) u := norm_nonneg _
  calc
    _ ≤ (∑ a, fourierSobolevNorm s (finiteL2CoordinateIsometry volume u a)) +
        ∑ i, ∑ a, fourierSobolevNorm s (w a i) :=
      add_le_add hunorm (Finset.sum_le_sum fun i _ ↦ hvnorm i)
    _ = ∑ a, (fourierSobolevNorm s (finiteL2CoordinateIsometry volume u a) +
        ∑ i, fourierSobolevNorm s (w a i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ _a : Fin r, (1 + 2 * Real.pi * n) * vectorFourierSobolevNorm (s + 1) u := by
      apply Finset.sum_le_sum
      intro a _
      exact (hn₂ a).trans (mul_le_mul_of_nonneg_left
        (fourierSobolevNorm_coordinate_le (s + 1) (finiteL2CoordinateIsometry volume u) a)
        (by positivity))
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith [mul_nonneg (show 0 ≤ 1 + 2 * Real.pi * n by positivity) hnonneg]

end JanetCartan.LocalSobolev
