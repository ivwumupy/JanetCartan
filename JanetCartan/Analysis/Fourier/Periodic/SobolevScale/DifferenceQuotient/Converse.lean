module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Translation
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# H¹ regularity from bounded difference quotients

The converse difference-quotient argument in
`app:ch_background:prop:bg-inverse` is proved on actual periodic L² classes.
For each finite frequency set, Parseval bounds the difference-quotient energy.
Passing to the scalar multiplier limit gives the coordinate derivative energy
bound. Summing over coordinates and adding the L² energy proves summability
of the H¹ Fourier weight and the explicit Sobolev norm estimate.

All arguments also apply to the zero-dimensional torus.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan

/-- The scalar multiplier limit used in the difference-quotient argument of
`app:ch_background:prop:bg-inverse`. -/
private theorem tendsto_sq_norm_exp_differenceQuotient (z : ℂ) :
    Tendsto (fun h : ℝ ↦ (|h|⁻¹ * ‖Complex.exp (z * h) - 1‖) ^ 2)
      (𝓝[≠] 0) (𝓝 (‖z‖ ^ 2)) := by
  have hd : HasDerivAt (fun h : ℝ ↦ Complex.exp (z * h)) z 0 := by
    have hc := ((hasDerivAt_id (0 : ℂ)).const_mul z).cexp
    simpa using hc.comp_ofReal
  simpa only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    norm_smul, Real.norm_eq_abs, abs_inv] using hd.tendsto_slope_zero.norm.pow 2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- Each Fourier energy tends to its coordinate derivative energy
(`app:ch_background:prop:bg-inverse`). -/
private theorem tendsto_sq_norm_periodicL2FourierCoeff_differenceQuotient
    (u : PeriodicL2 n F) (i : Fin n) (k : Fin n → ℤ) :
    Tendsto (fun h : ℝ ↦ ‖periodicL2FourierCoeff k
      (periodicL2DifferenceQuotient i h u)‖ ^ 2) (𝓝[≠] 0)
      (𝓝 ((2 * Real.pi * (k i : ℝ)) ^ 2 * ‖periodicL2FourierCoeff k u‖ ^ 2)) := by
  have hz : ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ ^ 2 =
      (2 * Real.pi * (k i : ℝ)) ^ 2 := by
    simp [mul_pow, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs]
  simpa only [norm_periodicL2FourierCoeff_differenceQuotient, mul_pow, hz] using
    (tendsto_sq_norm_exp_differenceQuotient (2 * Real.pi * Complex.I * (k i : ℂ))).mul_const
      (‖periodicL2FourierCoeff k u‖ ^ 2)

/-- Every finite coordinate derivative energy is bounded by the squared
quotient bound (`app:ch_background:prop:bg-inverse`). -/
private theorem sum_coordinateFourierEnergy_le_of_boundedDifferenceQuotients
    (u : PeriodicL2 n F) (C : ℝ) (hC : 0 ≤ C)
    (hδ : HasBoundedPeriodicDifferenceQuotients u C) (s : Finset (Fin n → ℤ))
    (i : Fin n) :
    ∑ k ∈ s, (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖periodicL2FourierCoeff k u‖ ^ 2 ≤ C ^ 2 := by
  apply le_of_tendsto (tendsto_finsetSum s
    (fun k _ ↦ tendsto_sq_norm_periodicL2FourierCoeff_differenceQuotient u i k))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < 1 := by
    filter_upwards [nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [hsmall, eventually_mem_nhdsWithin] with h hh hn
  have hne : h ≠ 0 := hn
  have hbound := hδ i h (abs_pos.mpr hne) hh.le
  have hp := hasSum_sq_periodicL2FourierCoeff (periodicL2DifferenceQuotient i h u)
  calc
    _ ≤ ‖periodicL2DifferenceQuotient i h u‖ ^ 2 := by
      rw [← hp.tsum_eq]
      exact hp.summable.sum_le_tsum s (fun k _ ↦ sq_nonneg _)
    _ ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg _) hC).mpr hbound

/-- Uniform finite H¹ energy bound before asserting summability
(`app:ch_background:prop:bg-inverse`). -/
private theorem sum_sobolevFourierEnergy_one_le_of_boundedDifferenceQuotients
    (u : PeriodicL2 n F) (C : ℝ) (hC : 0 ≤ C)
    (hδ : HasBoundedPeriodicDifferenceQuotients u C) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, (1 + frequencyNorm k ^ 2) * ‖periodicL2FourierCoeff k u‖ ^ 2 ≤
      ‖u‖ ^ 2 + (n : ℝ) * C ^ 2 := by
  have hp := hasSum_sq_periodicL2FourierCoeff u
  calc
    _ = (∑ k ∈ s, ‖periodicL2FourierCoeff k u‖ ^ 2) +
        ∑ i : Fin n, ∑ k ∈ s,
          (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖periodicL2FourierCoeff k u‖ ^ 2 := by
      simp_rw [add_mul, one_mul, frequencyNorm_sq_eq_sum, Finset.sum_mul]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ‖u‖ ^ 2 + ∑ _i : Fin n, C ^ 2 := by
      apply add_le_add
      · rw [← hp.tsum_eq]
        exact hp.summable.sum_le_tsum s (fun k _ ↦ sq_nonneg _)
      · exact Finset.sum_le_sum (fun i _ ↦
          sum_coordinateFourierEnergy_le_of_boundedDifferenceQuotients u C hC hδ s i)
    _ = _ := by simp

/-- Bounded small coordinate difference quotients imply membership in H¹
(`app:ch_background:prop:bg-inverse`). The proof first bounds finite Fourier sums
and only then obtains weighted summability. -/
theorem mem_periodicSobolevLevel_one_of_boundedDifferenceQuotients
    (u : PeriodicL2 n F) (C : ℝ) (hC : 0 ≤ C)
    (hδ : HasBoundedPeriodicDifferenceQuotients u C) :
    u ∈ periodicSobolevLevel n F 1 := by
  have hs : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) *
      ‖periodicL2FourierCoeff k u‖ ^ 2) :=
    summable_of_sum_le (fun k ↦ by positivity)
      (sum_sobolevFourierEnergy_one_le_of_boundedDifferenceQuotients u C hC hδ)
  rw [mem_periodicSobolevLevel_iff]
  simpa [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2] using hs

/-- The explicit H¹ bound recovered from bounded coordinate difference quotients
(`app:ch_background:prop:bg-inverse`), including in dimension zero. -/
theorem norm_periodicSobolevSpace_one_le_of_boundedDifferenceQuotients
    (u : PeriodicL2 n F) (C : ℝ) (hC : 0 ≤ C)
    (hδ : HasBoundedPeriodicDifferenceQuotients u C) :
    ‖PeriodicSobolevSpace.ofL2 1 u
      (mem_periodicSobolevLevel_one_of_boundedDifferenceQuotients u C hC hδ)‖ ≤
      Real.sqrt (‖u‖ ^ 2 + (n : ℝ) * C ^ 2) := by
  rw [PeriodicSobolevSpace.norm_eq, PeriodicSobolevSpace.toL2_ofL2, periodicSobolevNorm]
  apply Real.sqrt_le_sqrt
  have hb := Real.tsum_le_of_sum_le (fun k ↦ show
    0 ≤ (1 + frequencyNorm k ^ 2) * ‖periodicL2FourierCoeff k u‖ ^ 2 by positivity)
    (sum_sobolevFourierEnergy_one_le_of_boundedDifferenceQuotients u C hC hδ)
  simpa [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2] using hb

/-- The squared H¹ estimate from bounded coordinate difference quotients
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_sq_periodicSobolevSpace_one_le_of_boundedDifferenceQuotients
    (u : PeriodicL2 n F) (C : ℝ) (hC : 0 ≤ C)
    (hδ : HasBoundedPeriodicDifferenceQuotients u C) :
    ‖PeriodicSobolevSpace.ofL2 1 u
      (mem_periodicSobolevLevel_one_of_boundedDifferenceQuotients u C hC hδ)‖ ^ 2 ≤
      ‖u‖ ^ 2 + (n : ℝ) * C ^ 2 := by
  have h := norm_periodicSobolevSpace_one_le_of_boundedDifferenceQuotients u C hC hδ
  have hs : 0 ≤ ‖u‖ ^ 2 + (n : ℝ) * C ^ 2 := by positivity
  simpa only [Real.sq_sqrt hs] using
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr h

end JanetCartan
