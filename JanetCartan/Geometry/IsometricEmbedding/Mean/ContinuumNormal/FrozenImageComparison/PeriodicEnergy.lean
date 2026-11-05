module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.KernelEnergy

/-!
# The frozen periodic image energy comparison

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, `Channel` proves the
literal fixed-channel comparison and the complete three-term energy identity.
`KernelIdentity` identifies all three terms with the explicit compact kernel,
retaining both source masks. `KernelRegularity` proves its joint smoothness
from the fixed data and discharges the identity's continuity premise. The
compact-kernel estimate then bounds the energy difference by the squared L¹
norm of the cell zero extension, for every real torus L² input. The constant
depends only on the fixed outer data; no inner radius enters the comparison.
The zero-dimensional case is included.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

/-- In dimension zero both Hilbert spaces have only the zero vector. The
periodic-versus-Euclidean image energy error is therefore exactly zero. This
closes the degenerate branch without a positive-dimension hypothesis in the
comparison (`app:ch_background:prop:bg-frame`). -/
theorem fixedPeriodicEnergyDifference_zero_dim {R : ℝ}
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin 0 → Matrix (Fin 0) (Fin 0) ℝ) (f : OutputL2 0) :
    |‖(fixedPeriodicChannel hR hcell A).adjoint f‖ ^ 2 -
        ‖(fixedEuclideanChannel hR A).adjoint (toEuclidean (𝕜 := ℝ) f)‖ ^ 2| = 0 := by
  have hf : f = 0 := by
    apply Lp.ext
    exact Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _
  simp [hf]

/-- The full frozen periodic image energy differs from the masked Euclidean
energy by at most a fixed constant times the squared L¹ norm of the actual
cell zero extension (`app:ch_background:prop:bg-frame`). This is the periodic
correction used by the frozen image normal comparison. The explicit smooth
compact kernel accounts for `B D*`, `D B*`, and `D D*`, with both source masks;
its regularity and identification follow from the fixed data. The constant
is chosen before the input, with no inner radius or dimension restriction. -/
theorem exists_fixedPeriodicEnergyDifference_le_l1_sq {n : ℕ} {R : ℝ}
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : OutputL2 n,
      let u := toEuclidean (𝕜 := ℝ) f
      |‖(fixedPeriodicChannel hR hcell A).adjoint f‖ ^ 2 -
          ‖(fixedEuclideanChannel hR A).adjoint u‖ ^ 2| ≤
        C * (∫ x, ‖u x‖) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_compactKernel_energy_bound
    (fixedNormalCorrectionKernel hR A)
    (contDiff_fixedNormalCorrectionKernel hR hcell A).continuous
    (hasCompactSupport_fixedNormalCorrectionKernel hR A)
  refine ⟨C, hC, fun f ↦ ?_⟩
  dsimp only
  by_cases hn : n = 0
  · subst n
    rw [fixedPeriodicEnergyDifference_zero_dim hR hcell A f]
    exact mul_nonneg hC (sq_nonneg _)
  · rw [fixedPeriodicEnergyDifference_eq_inner_crossTerms (Nat.pos_of_ne_zero hn)
      hR hcell A f,
      fixedNormalCrossTerms_inner_eq_integral hR hcell A
        (fun i j ↦ (contDiff_fixedNormalCorrectionKernelEntry hR hcell A i j).continuous)]
    exact (hbound _ (integrable_zeroExtension f)).2

end JanetCartan.ContinuumNormal.FrozenImageComparison
