module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.PhysicalDerivatives

/-!
# Fourier regularity of the concrete zeroth-jet realization

The comparison constant for `app:ch_regular:eq:chain-tail` depends only on the
fixed coordinate map and the derivative order. Membership and the estimate
are proved from the actual completed derivatives and the Fourier gain-one API.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces FourierIntegral FiniteChain.Graph.KernelLimits Pseudodifferential

variable {d : ℕ}
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))

/-- The fixed coordinate-and-order cost for the completion-to-Fourier
comparison in `app:ch_regular:eq:chain-tail`. It precedes every operator,
scale, elapsed time, accuracy and datum, and is independent of channel count. -/
def fourierComparisonConstant (m : ℕ) : ℝ :=
  (1 + ∑ i : Fin (d + 1),
    directionCost (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i))) ^ m

/-- Positivity of the fixed comparison constant
(`app:ch_regular:eq:chain-tail`). -/
theorem fourierComparisonConstant_pos (m : ℕ) : 0 < fourierComparisonConstant J m := by
  have hs : 0 ≤ ∑ i : Fin (d + 1),
      directionCost (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) :=
    Finset.sum_nonneg (fun _ _ => directionCost_nonneg _)
  exact pow_pos (by linarith) m

variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

/-- The actual zeroth-jet realization of every completed classical field
belongs to Fourier Hᵐ with a fixed norm bound. The conclusion is derived from
actual distributional derivatives; no Sobolev comparison is an input
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem physicalZeroJet_fourier_bound (m : ℕ)
    (u : Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) :
    MemFourierSobolev (m : ℝ) (physicalZeroJet J hJ m u) ∧
      fourierSobolevNorm (m : ℝ) (physicalZeroJet J hJ m u) ≤
        fourierComparisonConstant J m * ‖u‖ := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa only [Nat.cast_zero] using memFourierSobolev_zero (physicalZeroJet J hJ 0 u)
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero, fourierComparisonConstant,
      pow_zero, one_mul] using norm_physicalZeroJet_le J hJ 0 u
  | succ m ih =>
    let v (i : Fin (d + 1)) := completedDirectionalDerivative m
      (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) u
    have hbase : MemFourierSobolev (m : ℝ) (physicalZeroJet J hJ (m + 1) u) := by
      rw [← physicalZeroJet_lowerOrder J hJ m u]
      exact (ih (lowerOrder m u)).1
    have hbaseBound : fourierSobolevNorm (m : ℝ) (physicalZeroJet J hJ (m + 1) u) ≤
        fourierComparisonConstant J m * ‖u‖ := by
      rw [← physicalZeroJet_lowerOrder J hJ m u]
      exact (ih (lowerOrder m u)).2.trans (mul_le_mul_of_nonneg_left
        (norm_lowerOrder_apply_le m u) (fourierComparisonConstant_pos J m).le)
    have hv (i : Fin (d + 1)) := ih (v i)
    have hd (i : Fin (d + 1)) := physicalZeroJet_hasCoordinateDerivative J hJ m i u
    have hb (i : Fin (d + 1)) :
        fourierSobolevNorm (m : ℝ) (physicalZeroJet J hJ m (v i)) ≤
          fourierComparisonConstant J m *
            (directionCost (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) * ‖u‖) :=
      (hv i).2.trans (mul_le_mul_of_nonneg_left
        (norm_completedDirectionalDerivative_apply_le m _ u)
        (fourierComparisonConstant_pos J m).le)
    rw [Nat.cast_succ]
    refine ⟨hbase.of_coordinateDerivatives (by positivity) (fun i => (hv i).1) hd, ?_⟩
    calc
      _ ≤ fourierSobolevNorm (m : ℝ) (physicalZeroJet J hJ (m + 1) u) +
          ∑ i, fourierSobolevNorm (m : ℝ) (physicalZeroJet J hJ m (v i)) :=
        fourierSobolevNorm_le_coordinateDerivatives (by positivity) hbase
          (fun i => (hv i).1) hd
      _ ≤ fourierComparisonConstant J m * ‖u‖ +
          ∑ i : Fin (d + 1), fourierComparisonConstant J m *
            (directionCost (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) * ‖u‖) :=
        add_le_add hbaseBound (Finset.sum_le_sum (fun i _ => hb i))
      _ = fourierComparisonConstant J (m + 1) * ‖u‖ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        simp only [fourierComparisonConstant, pow_succ]
        ring

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
