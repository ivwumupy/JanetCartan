module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.SmoothMajorant

/-!
# Fixed spectator support of the Euclidean full bands

The fixed spectator integral after `app:ch_waves:eq:sampling-operator-bounds`
is over a bounded set chosen with the angular cutoff, before any frequencies
or colors. These are support deductions from the actual forward columns,
used by the final full-phase assembly and its dyadic-estimate consumer.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds SeparatedSampling BackgroundQuadrature ContinuumRow

/-- The original angular support bounds give a fixed Euclidean spectator
ball. Its radius is independent of the band and color
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem patchWeight_eq_zero_off_spectator_ball {χ : Point → ℝ} {R P : ℝ}
    (hχ : PatchBounds χ R P) {v : Euclidean 2}
    (hv : v ∉ Metric.closedBall 0 (2 * R)) (s : ℝ) :
    χ (carrierSamplingEquiv (s, v)) = 0 := by
  by_contra hz
  have h₀ := hχ.support _ hz (1 : Fin 3)
  have h₁ := hχ.support _ hz (2 : Fin 3)
  simp only [carrierSamplingEquiv_apply, Fin.cons_one] at h₀ h₁
  have hs₀ : (v 0) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v 0)) hχ.radius_nonneg).mpr h₀
  have hs₁ : (v 1) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v 1)) hχ.radius_nonneg).mpr h₁
  have hn := EuclideanSpace.real_norm_sq_eq v
  simp only [Fin.sum_univ_two] at hn
  apply hv
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg v, hχ.radius_nonneg]

/-- The full-band forward map itself vanishes outside the fixed spectator
ball, by its literal kernel formula. No operator support premise is assumed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem fullBandKernelOperator_eq_zero_off_spectator_ball
    {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q] [LocallyCompactSpace Q]
    {n : ℕ} (D : BandKernelData Q n) (q : Point → Q) (hq : Continuous q)
    {χ : Point → ℝ} {R P : ℝ} (hχ : PatchBounds χ R P) (hχc : Continuous χ)
    (j : ℕ) {v : Euclidean 2} (hv : v ∉ Metric.closedBall 0 (2 * R)) :
    fullBandKernelOperator D q hq χ hχc j R v = 0 := by
  ext1 f
  rw [fullBandKernelOperator_apply]
  simp only [fullBandColumn, patchWeight_eq_zero_off_spectator_ball hχ hv,
    zero_smul, smul_zero, integral_zero, zero_apply]

end JanetCartan.Sampling.MeanNormalBound
