module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail.Identity

/-!
# Source-mask defect of the frozen Euclidean normal

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, the literal masked and
uncut Euclidean adjoint energies differ by at most a fixed constant times the
squared L¹ norm of any real L² input supported in the input ball. The constant
depends only on the fixed radius and constant differential coefficients.

The exact mask factorization removes the measurement mask by its plateau.
The remaining original source square stays between the two Bessel factors;
the auxiliary cutoff separates its defect from both input endpoints. The
checked differentiated kernel is continuous and compactly supported, and
its energy identity extends from compact smooth tests to supported L² data.
Supported L² inputs are integrable, so the compact-kernel bound applies.
Consumer: the frozen periodic image normal comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

/-- The source-mask contribution to the frozen image normal comparison in
`paper-v2.tex`, `app:ch_background:prop:bg-frame`, is bounded by the squared
L¹ norm on every supported real L² input. The measurement and source masks
remain `FixedCutoffs.physical hR 1` and `FixedCutoffs.physical hR 2`.
The constant is selected before the input, with no dimension restriction or
additional integrability or analytic hypothesis. -/
theorem exists_fixedSourceEnergyDifference_le_l1_sq {n : ℕ} {R : ℝ}
    (hR : 0 < R) (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanL2 n (EuclideanSpace ℝ (Fin n)),
      (∀ᵐ x ∂volume, x ∉ ball (0 : EuclideanSpace ℝ (Fin n)) R → u x = 0) →
      |‖(fixedEuclideanChannel hR A).adjoint u‖ ^ 2 -
          ‖(uncutRealChannel A).adjoint u‖ ^ 2| ≤
        C * (∫ x, ‖u x‖) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_fixedSourceTail_kernel_bound hR A
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  rw [abs_sub_comm, fixedEuclideanChannel_energy_defect_eq_kernel hR A u hu]
  exact (hbound u hu).2

end JanetCartan.ContinuumNormal.FrozenImageComparison
