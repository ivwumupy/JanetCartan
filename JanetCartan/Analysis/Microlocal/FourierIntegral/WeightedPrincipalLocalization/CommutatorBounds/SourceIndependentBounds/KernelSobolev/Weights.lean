module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.CommutatorBounds.SourceIndependentBounds.FourierDecay
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Basic

/-!
# Weights for the source-independent frequency-kernel estimate

The kernel estimates in Steps 1 and 3 of
`app:ch_regular_base:thm:actual-calculus` use `(1 + ‖ξ‖)^s`, whereas the
existing Fourier Sobolev spaces use `(1 + ‖ξ‖²)^(s/2)`. These comparisons
retain the single high factor in `app:ch_regular_base:eq:actual-one-high`.
The consumers are the forward weighted integral estimate and the literal
adjoint identification in `KernelSobolev`.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Natural Bessel weights are powers of the order-one weight, including
order zero in `app:ch_regular_base:eq:fio-input`. -/
theorem euclideanSobolevWeight_nat_eq_pow (s : ℕ) (ξ : E) :
    euclideanSobolevWeight (s : ℝ) ξ = euclideanSobolevWeight 1 ξ ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.cast_add_one, euclideanSobolevWeight_add, ih, pow_succ]

/-- The output Bessel weight is controlled by the weight of the actual
frequency kernel in `app:ch_regular_base:eq:fio-input`. -/
theorem euclideanSobolevWeight_nat_le_one_add_norm_pow (s : ℕ) (ξ : E) :
    euclideanSobolevWeight (s : ℝ) ξ ≤ (1 + ‖ξ‖) ^ s := by
  rw [euclideanSobolevWeight_nat_eq_pow]
  have hsq : euclideanSobolevWeight 1 ξ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [euclideanSobolevWeight, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  apply pow_le_pow_left₀ (euclideanSobolevWeight_pos _ _).le
  nlinarith [euclideanSobolevWeight_pos 1 ξ, norm_nonneg ξ]

/-- The input polynomial weight costs only a fixed order-dependent factor
in `app:ch_regular_base:eq:fio-input`; this factor is independent of the
amplitude, high budget and realized operator. -/
theorem one_add_norm_pow_le_two_pow_mul_euclideanSobolevWeight (s : ℕ) (ξ : E) :
    (1 + ‖ξ‖) ^ s ≤ 2 ^ s * euclideanSobolevWeight (s : ℝ) ξ := by
  rw [euclideanSobolevWeight_nat_eq_pow, ← mul_pow]
  have hsq : euclideanSobolevWeight 1 ξ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [euclideanSobolevWeight, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  have hn : ‖ξ‖ ≤ euclideanSobolevWeight 1 ξ := by
    nlinarith [euclideanSobolevWeight_pos 1 ξ, norm_nonneg ξ]
  have h1 : 1 ≤ euclideanSobolevWeight 1 ξ := by
    simpa using euclideanSobolevWeight_mono (d := n) (show (0 : ℝ) ≤ 1 by norm_num) ξ
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- Converting both kernel weights preserves the additive high budget in
`app:ch_regular_base:eq:actual-one-high`. This is the pointwise input to the
weighted integral proof of `app:ch_regular_base:eq:fio-input`. -/
theorem bessel_weighted_frequencyKernel_bound (s : ℕ) (C H z : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hz : 0 ≤ z) (ξ η : E)
    (hk : (1 + ‖ξ‖) ^ (s + 1) * z ≤
      C * ((1 + ‖η‖) ^ s + H) * frequencyDifferenceMajorant (ξ - η)) :
    euclideanSobolevWeight ((s : ℝ) + 1) ξ * z ≤
      (C * 2 ^ s) * (euclideanSobolevWeight (s : ℝ) η + H) *
        frequencyDifferenceMajorant (ξ - η) := by
  have hw : euclideanSobolevWeight ((s : ℝ) + 1) ξ ≤ (1 + ‖ξ‖) ^ (s + 1) := by
    simpa only [Nat.cast_add_one] using
      euclideanSobolevWeight_nat_le_one_add_norm_pow (s + 1) ξ
  have hi : (1 + ‖η‖) ^ s + H ≤
      2 ^ s * (euclideanSobolevWeight (s : ℝ) η + H) := by
    have hpow : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    have hweight := one_add_norm_pow_le_two_pow_mul_euclideanSobolevWeight s η
    nlinarith [mul_le_mul_of_nonneg_right hpow hH]
  calc
    _ ≤ (1 + ‖ξ‖) ^ (s + 1) * z := mul_le_mul_of_nonneg_right hw hz
    _ ≤ C * ((1 + ‖η‖) ^ s + H) * frequencyDifferenceMajorant (ξ - η) := hk
    _ ≤ C * (2 ^ s * (euclideanSobolevWeight (s : ℝ) η + H)) *
        frequencyDifferenceMajorant (ξ - η) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hC)
        (frequencyDifferenceMajorant_nonneg _)
    _ = _ := by ring

/-- The difference-frequency majorant is bounded by one. Together with
Schwartz decay, this gives absolute integrability of the adjoint pairings
in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem frequencyDifferenceMajorant_le_one (ξ : E) :
    frequencyDifferenceMajorant ξ ≤ 1 := by
  unfold frequencyDifferenceMajorant
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp)
    (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])

/-- The fixed majorant belongs to L² as well as L¹. This supplies the
integrability input for identifying the literal reverse kernel on Schwartz
tests in `app:ch_regular_base:eq:fio-input`. -/
theorem memLp_frequencyDifferenceMajorant :
    MemLp (frequencyDifferenceMajorant (n := n)) 2 volume := by
  have hi := integrable_frequencyDifferenceMajorant (n := n)
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  apply hi.mono' (hi.aestronglyMeasurable.pow 2)
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change frequencyDifferenceMajorant ξ ^ 2 ≤ frequencyDifferenceMajorant ξ
  nlinarith [frequencyDifferenceMajorant_nonneg ξ, frequencyDifferenceMajorant_le_one ξ]

end JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
