module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Forward
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Converse

/-!
# H¹ characterization by periodic L² difference quotients

For the order-one argument in `app:ch_background:prop:bg-inverse`, an actual
periodic L² class belongs to H¹ if and only if all coordinate difference
quotients with `0 < |h| ≤ 1` have a common nonnegative real bound.

The imported leaves construct translations as linear isometries for normalized
torus volume and prove their Fourier identities in the real-pair convention.
The forward estimate bounds every nonzero-step quotient by the H¹ norm.
The converse establishes weighted summability from finite Fourier sums and
gives the explicit H¹ bound `Real.sqrt (‖u‖ ^ 2 + (n : ℝ) * C ^ 2)`.
These statements include dimension zero and arbitrary finite-dimensional real
Hilbert targets.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- An L² class in H¹ has bounded small coordinate difference quotients, with
its H¹ norm as bound (`app:ch_background:prop:bg-inverse`). -/
theorem hasBoundedPeriodicDifferenceQuotients_of_mem (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F 1) :
    HasBoundedPeriodicDifferenceQuotients u ‖PeriodicSobolevSpace.ofL2 1 u hu‖ := by
  simpa only [PeriodicSobolevSpace.toL2_ofL2] using
    hasBoundedPeriodicDifferenceQuotients_toL2 (PeriodicSobolevSpace.ofL2 1 u hu)

/-- H¹ membership is equivalent to a uniform nonnegative real bound on all
coordinate difference quotients with `0 < |h| ≤ 1`
(`app:ch_background:prop:bg-inverse`). The equivalence also holds in dimension zero. -/
theorem mem_periodicSobolevLevel_one_iff_boundedDifferenceQuotients (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F 1 ↔
      ∃ C : ℝ, 0 ≤ C ∧ HasBoundedPeriodicDifferenceQuotients u C := by
  constructor
  · intro hu
    exact ⟨‖PeriodicSobolevSpace.ofL2 1 u hu‖, norm_nonneg _,
      hasBoundedPeriodicDifferenceQuotients_of_mem u hu⟩
  · rintro ⟨C, hC, hδ⟩
    exact mem_periodicSobolevLevel_one_of_boundedDifferenceQuotients u C hC hδ

end JanetCartan
