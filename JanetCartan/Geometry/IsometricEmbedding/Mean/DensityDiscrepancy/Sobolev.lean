module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Preparation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Sobolev
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Space

/-!
# The shared Sobolev realization for density preparation

Use these maps for `Y`, `realize`, `q`, and `hq` in
`exists_preparation_discrepancy_inputs`. The measured residual is a singleton
smooth periodic family, and its realization has exactly the shared Fourier
Sobolev norm. This concerns only the output; the carrier/initial integration
measure in the discrepancy remains the literal input measure.
-/

@[expose] public noncomputable section
namespace JanetCartan.DensityDiscrepancy
open CurrentMean CurrentMean.SmoothPeriodicFamily

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G]

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: realize a smooth measured
residual in the existing `H^s` space, retaining its actual L² representative. -/
def densitySobolevRealization (s : ℕ) :
    SmoothPeriodicFamily n Unit G →ₗ[ℝ] PeriodicSobolevSpace n G s :=
  (PeriodicSobolevSpace.toLevel s).symm.toLinearMap.comp (componentSobolev s ())

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: the realization is of the
actual smooth residual, with no change of Fourier convention or initial measure. -/
theorem densitySobolevRealization_toL2 (s : ℕ) (e : SmoothPeriodicFamily n Unit G) :
    PeriodicSobolevSpace.toL2 s (densitySobolevRealization s e) = componentL2 () e := rfl

/-- `app:ch_mean_pairs:eq:mean-density-lipschitz`: exact Fourier `H^s` norm
of the residual realization. -/
theorem norm_densitySobolevRealization (s : ℕ) (e : SmoothPeriodicFamily n Unit G) :
    ‖densitySobolevRealization s e‖ = periodicSobolevNorm s (fun x ↦ e.val x ()) := by
  rw [PeriodicSobolevSpace.norm_eq, densitySobolevRealization_toL2]
  unfold periodicSobolevNorm
  simp only [periodicFourierCoeff_congr_ae (componentL2_coe_ae () e)]

/-- `app:ch_mean_pairs:prop:mean-coarse`: the exact `hq` input for
`exists_preparation_discrepancy_inputs`, using the shared smooth-family Sobolev
seminorm. Thus its conclusions are literally the `hE` and `hinit` preparation
premises for the actual Fourier `H^s` sizes. -/
theorem densitySobolevSeminorm_eq_norm (s : ℕ) (e : SmoothPeriodicFamily n Unit G) :
    sobolevSeminorm (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) s e =
      ‖densitySobolevRealization s e‖ := by
  rw [sobolevSeminorm_eq, norm_densitySobolevRealization, weightedPeriodicSobolevNorm]
  simp only [Fintype.sum_unique, one_mul, Real.sqrt_sq
    (show 0 ≤ periodicSobolevNorm s (fun x ↦ e.val x ()) from Real.sqrt_nonneg _)]

end JanetCartan.DensityDiscrepancy
