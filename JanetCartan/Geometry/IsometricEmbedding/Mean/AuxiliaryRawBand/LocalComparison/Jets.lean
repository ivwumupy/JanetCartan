module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Cartesian
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.NormComparison
public import JanetCartan.Analysis.Fourier.Periodic.Calculus

/-!
# Operator jet bounds on the unit cell

The cutoff extension for `app:ch_background:prop:bg-mixed-physical` uses
operator jets. The existing symmetric-jet comparison gives an explicit
constant depending only on dimension and order, including dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Periodic smooth Fréchet jets are square integrable on the physical unit
cell (`app:ch_background:prop:bg-mixed-physical`). -/
theorem memLp_iteratedFDeriv_periodicLift_cell {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (j : ℕ) :
    MemLp (iteratedFDeriv ℝ j (periodicLift f)) 2 (volume.restrict (halfOpenCell n)) := by
  have hc := hf.2.continuous_iteratedFDeriv (m := j) (by simp)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (ContinuousOn.integrableOn_compact (isCompact_fundamentalCell n)
    (hc.norm.pow 2).continuousOn).mono_set halfOpenCell_subset_fundamentalCell

/-- The half-open cell's Cartesian energy is bounded with constant one
(`app:not:fourier`). This also covers the cell's nonopen boundary. -/
theorem cartesianJetNorm_periodicLift_cell_le {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (s : ℕ) :
    cartesianJetNorm (halfOpenCell n) s (fun j ↦ iteratedFDeriv ℝ j (periodicLift f)) ≤
      periodicDerivativeL2Norm s f := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α _
  rw [cartesianJetDerivative_periodicLift hf]
  exact integral_norm_sq_periodicLift_le (hf.multiindexDeriv _).1 (Subset.refl _)

end JanetCartan.AuxiliaryRawBand

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Explicit operator-jet comparison for the physical cutoff extension
(`app:ch_background:prop:bg-mixed-physical`). The constant is independent of
both output fibers, so it applies to vectors and Frobenius tensors alike. -/
theorem jetL2Norm_periodicLift_cell_le {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (s : ℕ) :
    jetL2Norm (halfOpenCell n) s (fun j ↦ iteratedFDeriv ℝ j (periodicLift f)) ≤
      Real.sqrt ((s + 1) * BallExtension.frechetEnergyComparisonConstant n s) *
        periodicSobolevNorm s f := by
  apply (jetL2Norm_le_mul_cartesianJetNorm_of_symmetric measurableSet_halfOpenCell s _
    (fun j _ ↦ memLp_iteratedFDeriv_periodicLift_cell hf j) ?_).trans
  · exact mul_le_mul_of_nonneg_left
      ((cartesianJetNorm_periodicLift_cell_le hf s).trans
        (periodicDerivativeL2Norm_le_periodicSobolevNorm hf s)) (Real.sqrt_nonneg _)
  · intro x _ j _ v σ
    simpa only [iteratedFDerivWithin_univ] using
      BallExtension.iteratedFDerivWithin_comp_perm_of_contDiffOn isOpen_univ
        hf.2.contDiffOn (mem_univ x) j v σ

end JanetCartan.AuxiliaryRawBand
