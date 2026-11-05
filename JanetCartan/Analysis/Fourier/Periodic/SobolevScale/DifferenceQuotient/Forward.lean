module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Translation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sobolev bounds for periodic difference quotients

For the order-one difference-quotient argument in
`app:ch_background:prop:bg-inverse`, every coordinate difference quotient of an
H¹ element has L² norm at most its H¹ norm. The proof compares the Fourier
multiplier with the Sobolev weight and applies Parseval to convergent series.
-/

@[expose] public noncomputable section

open scoped ENNReal
namespace JanetCartan

/-- The coordinate difference-quotient multiplier is bounded by the order-one
Sobolev weight (`app:ch_background:prop:bg-inverse`; `app:not:fourier`). -/
private theorem differenceQuotientMultiplier_le_weight {n : ℕ} (i : Fin n)
    (h : ℝ) (hh : h ≠ 0) (k : Fin n → ℤ) :
    |h|⁻¹ * ‖Complex.exp (2 * Real.pi * Complex.I * (k i : ℂ) * h) - 1‖ ≤
      periodicSobolevWeight 1 k := by
  have harg : (2 * Real.pi * Complex.I * (k i : ℂ) * h) =
      Complex.I * ((2 * Real.pi * (k i : ℝ) * h : ℝ) : ℂ) := by
    push_cast
    ring
  have hfreq : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ frequencyNorm k ^ 2 := by
    rw [frequencyNorm_sq_eq_sum]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (2 * Real.pi * (k j : ℝ)))
      (Finset.mem_univ i)
  calc
    _ ≤ |h|⁻¹ * |2 * Real.pi * (k i : ℝ) * h| := by
      rw [harg]
      exact mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le
        (inv_nonneg.mpr (abs_nonneg h))
    _ = |2 * Real.pi * (k i : ℝ)| := by
      rw [abs_mul, mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr hh), mul_one]
    _ ≤ periodicSobolevWeight 1 k := by
      apply (sq_le_sq₀ (abs_nonneg _) (periodicSobolevWeight_pos 1 k).le).mp
      rw [sq_abs, periodicSobolevWeight_sq]
      norm_num only [Nat.cast_one, Real.rpow_one]
      linarith

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Every nonzero coordinate difference quotient of an H¹ element is bounded in
L² by its H¹ norm (`app:ch_background:prop:bg-inverse`). The estimate holds for
all step sizes and in every dimension. -/
theorem norm_periodicL2DifferenceQuotient_le_sobolev
    (u : PeriodicSobolevSpace n F 1) (i : Fin n) (h : ℝ) (hh : h ≠ 0) :
    ‖periodicL2DifferenceQuotient i h (PeriodicSobolevSpace.toL2 1 u)‖ ≤ ‖u‖ := by
  have hcoeff (k : Fin n → ℤ) :
      ‖periodicL2FourierCoeff k
        (periodicL2DifferenceQuotient i h (PeriodicSobolevSpace.toL2 1 u))‖ ≤
      ‖PeriodicSobolevSpace.analysis 1 u k‖ := by
    rw [norm_periodicL2FourierCoeff_differenceQuotient,
      PeriodicSobolevSpace.analysis_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (periodicSobolevWeight_pos 1 k)]
    exact mul_le_mul_of_nonneg_right (differenceQuotientMultiplier_le_weight i h hh k)
      (norm_nonneg _)
  have hu : HasSum (fun k ↦ ‖PeriodicSobolevSpace.analysis 1 u k‖ ^ 2) (‖u‖ ^ 2) := by
    have hn : ‖PeriodicSobolevSpace.analysis 1 u‖ = ‖u‖ :=
      (PeriodicSobolevSpace.analysisIsometry 1).norm_map u
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hn] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
        (PeriodicSobolevSpace.analysis 1 u)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact hasSum_le (fun k ↦ (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hcoeff k))
    (hasSum_sq_periodicL2FourierCoeff _) hu

/-- H¹ elements have uniformly bounded small coordinate difference quotients,
with their Sobolev norm as the bound (`app:ch_background:prop:bg-inverse`). -/
theorem hasBoundedPeriodicDifferenceQuotients_toL2 (u : PeriodicSobolevSpace n F 1) :
    HasBoundedPeriodicDifferenceQuotients (PeriodicSobolevSpace.toL2 1 u) ‖u‖ := by
  intro i h hh _
  exact norm_periodicL2DifferenceQuotient_le_sobolev u i h (abs_pos.mp hh)

end JanetCartan
