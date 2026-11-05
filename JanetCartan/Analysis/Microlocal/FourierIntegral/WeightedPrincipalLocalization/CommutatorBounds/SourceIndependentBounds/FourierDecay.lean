module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceDecay
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Physical Fourier decay for the source-independent commutator

The source-independent PDO in `app:ch_regular_base:eq:fio-input` has a
frequency kernel obtained by Fourier transforming only its physical output
variable. The finite physical jets give the integrable difference-frequency
majorant below. No support or derivatives in the input position are required.

The consumer is the gain-one bound for the literal principal commutator.
Physical covectors are rescaled by `2π` in `sourceIndependentFourierKernel`,
so its arguments use Mathlib's Fourier convention.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
open JanetCartan.Pseudodifferential

namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds

variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The fixed physical reserve for the source-independent gain-one estimate
in `app:ch_regular_base:eq:fio-input`. -/
def physicalJetReserve (n : ℕ) : ℕ := n + 2

/-- The integrable difference-frequency majorant used in Steps 1 and 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
def frequencyDifferenceMajorant (θ : E) : ℝ :=
  (1 + ‖θ‖) ^ (-((n : ℝ) + 1))

/-- The majorant is integrable in every dimension, including at zero
frequency (`app:ch_regular_base:eq:fio-input`). -/
theorem integrable_frequencyDifferenceMajorant :
    Integrable (frequencyDifferenceMajorant (n := n)) := by
  exact integrable_one_add_norm (by simp)

/-- Nonnegativity of the Schur majorant for
`app:ch_regular_base:eq:fio-input`. -/
theorem frequencyDifferenceMajorant_nonneg (θ : E) :
    0 ≤ frequencyDifferenceMajorant θ := by
  unfold frequencyDifferenceMajorant
  positivity

/-- Reversing the frequency kernel preserves its majorant. This is used for
the literal adjoint in `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyDifferenceMajorant_sub_comm (ξ η : E) :
    frequencyDifferenceMajorant (ξ - η) = frequencyDifferenceMajorant (η - ξ) := by
  simp only [frequencyDifferenceMajorant, norm_sub_rev]

/-- The literal normalized frequency kernel for the linear phase in
`app:ch_regular_base:thm:actual-calculus`. Its operator realization is a
separate Fourier/Fubini identity. -/
def sourceIndependentFourierKernel (b : E → E → Mat) (ξ η : E) : Mat :=
  𝓕 (fun x ↦ b x ((2 * Real.pi) • η)) (ξ - η)

/-- Joint measurability of the actual frequency kernel, used for the Schur
integrals in `app:ch_regular_base:eq:fio-input`. -/
theorem stronglyMeasurable_sourceIndependentFourierKernel (b : E → E → Mat)
    (hb : Continuous (Function.uncurry b)) :
    StronglyMeasurable (Function.uncurry (sourceIndependentFourierKernel b)) := by
  simp only [Function.uncurry_def, sourceIndependentFourierKernel, Real.fourier_eq]
  apply StronglyMeasurable.integral_prod_right
  apply Continuous.stronglyMeasurable
  exact (Real.continuous_fourierChar.comp (by fun_prop)).smul
    (hb.comp (f := fun p : (E × E) × E ↦ (p.2, (2 * Real.pi) • p.1.2)) (by fun_prop))

/-- The finite output-jet constant for the Fourier-kernel estimate in
`app:ch_regular_base:eq:fio-input`; it depends only on radius, order and
dimension. -/
def physicalFourierDecayConstant (n : ℕ) (R : ℝ) (q : ℕ) : ℝ :=
  (2 ^ (q - 1) * (1 + 2 ^ q)) * ((q + 1 : ℕ) : ℝ) *
    volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)

/-- Positivity in the non-strict sense suffices for the Fourier decay
constant in `app:ch_regular_base:eq:fio-input`. -/
theorem physicalFourierDecayConstant_nonneg (R : ℝ) (q : ℕ) :
    0 ≤ physicalFourierDecayConstant n R q := by
  unfold physicalFourierDecayConstant
  positivity

private theorem physicalSlice_support (b : E → E → Mat) (R : ℝ)
    (hs : ∀ x η, R < ‖x‖ → b x η = 0) (η : E) :
    tsupport (fun x ↦ b x η) ⊆ Metric.closedBall (0 : E) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt (fun h ↦ hx (hs x η h))

private theorem physicalSlice_mass_le (b : E → E → Mat) (R : ℝ)
    (hs : ∀ x η, R < ‖x‖ → b x η = 0) (q : ℕ) (B : ℝ) (η : E)
    (hB : ∀ j ≤ q, ∀ x, ‖iteratedFDeriv ℝ j (fun z ↦ b z η) x‖ ≤ B) :
    sourceDerivativeMass (fun x ↦ b x η) q ≤
      ((q + 1 : ℕ) : ℝ) * volume.real (Metric.closedBall (0 : E) R) * B := by
  have hs' := physicalSlice_support b R hs η
  have hi (j : ℕ) (hj : j ≤ q) :
      (∫ x, ‖iteratedFDeriv ℝ j (fun z ↦ b z η) x‖) ≤
        volume.real (Metric.closedBall (0 : E) R) * B := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : E) R)
      (fun x hx ↦ by
        rw [image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx (hs' (tsupport_iteratedFDeriv_subset j h))), norm_zero])]
    calc
      _ ≤ ‖∫ x in Metric.closedBall (0 : E) R,
          ‖iteratedFDeriv ℝ j (fun z ↦ b z η) x‖‖ := le_abs_self _
      _ ≤ B * volume.real (Metric.closedBall (0 : E) R) := by
        apply norm_setIntegral_le_of_norm_le_const
          (isCompact_closedBall (0 : E) R).measure_lt_top
        intro x _
        simpa only [norm_norm] using hB j hj x
      _ = _ := mul_comm _ _
  unfold sourceDerivativeMass
  calc
    _ ≤ ∑ j ∈ Finset.range (q + 1),
        volume.real (Metric.closedBall (0 : E) R) * B :=
      Finset.sum_le_sum (fun j hj ↦ hi j (by simpa using Finset.mem_range.mp hj))
    _ = _ := by simp [mul_assoc]

/-- Physical order-minus-one jets give weighted Fourier decay using exactly
`q` output derivatives. This supplies the low and high kernel bounds in
`app:ch_regular_base:eq:fio-input`, without any frequency-jet premise. -/
theorem physical_fourier_decay_of_weighted_jets
    (b : E → E → Mat) (R : ℝ) (q : ℕ)
    (hb : ∀ η, ContDiff ℝ q (fun x ↦ b x η))
    (hs : ∀ x η, R < ‖x‖ → b x η = 0) (B : ℝ)
    (hB : ∀ η j, j ≤ q → ∀ x,
      (1 + ‖η‖) * ‖iteratedFDeriv ℝ j (fun z ↦ b z η) x‖ ≤ B)
    (θ η : E) :
    (1 + ‖θ‖) ^ q * ((1 + ‖η‖) * ‖𝓕 (fun x ↦ b x η) θ‖) ≤
      physicalFourierDecayConstant n R q * B := by
  have hp : 0 < 1 + ‖η‖ := by positivity
  have hc : HasCompactSupport (fun x ↦ b x η) :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport _)
      (physicalSlice_support b R hs η)
  have hm := physicalSlice_mass_le b R hs q (B / (1 + ‖η‖)) η
    (fun j hj x ↦ (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hB η j hj x))
  have hd := one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    (fun x ↦ b x η) q (hb η)
    (fun j hj ↦ ((hb η).continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j)) θ
  have ht := mul_le_mul_of_nonneg_left
    (hd.trans (mul_le_mul_of_nonneg_left hm (by positivity))) hp.le
  calc
    _ = (1 + ‖η‖) * ((1 + ‖θ‖) ^ q * ‖𝓕 (fun x ↦ b x η) θ‖) := by ring
    _ ≤ (1 + ‖η‖) * ((2 ^ (q - 1) * (1 + 2 ^ q)) *
        (((q + 1 : ℕ) : ℝ) * volume.real (Metric.closedBall (0 : E) R) *
          (B / (1 + ‖η‖)))) := ht
    _ = _ := by
      unfold physicalFourierDecayConstant
      field_simp

/-- Spending `k` difference-frequency powers leaves an integrable majorant
from `k+n+1` physical derivatives. The forward gain-one consumer takes
`k=s+1`, hence the reserve `μ=n+2` is fixed before `s`.
Source: `app:ch_regular_base:eq:fio-input` and `actual-one-high`. -/
theorem sourceIndependentFourierKernel_moment_le
    (b : E → E → Mat) (R : ℝ) (k : ℕ)
    (hb : ∀ η, ContDiff ℝ (k + n + 1) (fun x ↦ b x η))
    (hs : ∀ x η, R < ‖x‖ → b x η = 0) (B : ℝ)
    (hB : ∀ η j, j ≤ k + n + 1 → ∀ x,
      (1 + ‖η‖) * ‖iteratedFDeriv ℝ j (fun z ↦ b z η) x‖ ≤ B)
    (ξ η : E) :
    (1 + ‖ξ - η‖) ^ k * ((1 + ‖η‖) * ‖sourceIndependentFourierKernel b ξ η‖) ≤
      physicalFourierDecayConstant n R (k + n + 1) * B *
        frequencyDifferenceMajorant (ξ - η) := by
  have hp : 0 < 1 + ‖ξ - η‖ := by positivity
  have hη : 1 + ‖η‖ ≤ 1 + ‖(2 * Real.pi) • η‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.two_le_pi, norm_nonneg η]
  have hd := physical_fourier_decay_of_weighted_jets b R (k + n + 1) hb hs B hB
    (ξ - η) ((2 * Real.pi) • η)
  have hnorm : (1 + ‖ξ - η‖) ^ (k + n + 1) *
      ((1 + ‖η‖) * ‖sourceIndependentFourierKernel b ξ η‖) ≤
      physicalFourierDecayConstant n R (k + n + 1) * B := by
    apply le_trans _ hd
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hη (norm_nonneg _)) (pow_nonneg hp.le _)
  have he : frequencyDifferenceMajorant (ξ - η) =
      ((1 + ‖ξ - η‖) ^ (n + 1))⁻¹ := by
    rw [frequencyDifferenceMajorant, ← Nat.cast_add_one,
      Real.rpow_neg hp.le, Real.rpow_natCast]
  rw [he, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp (n + 1))]
  convert hnorm using 1
  simp [pow_add, mul_assoc, mul_left_comm, mul_comm]

end JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
