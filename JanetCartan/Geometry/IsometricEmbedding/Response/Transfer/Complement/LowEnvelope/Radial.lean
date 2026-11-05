module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel
public import JanetCartan.Analysis.Microlocal.Localization.RadialIntegral

/-!
# Radial integration of low-envelope kernel bounds

The frequency summation in `app:ch_response:thm:response-literal-transfer`.
Taking `q + s + n + 1` source integrations pays for the output order `s` and
Lebesgue frequency integration, with a remaining power `ρ^(s+n)` independent
of `q`. The integral covers the entire frequency space, including zero and
all radial and angular shoulders.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral JanetCartan.Localization

/-- Dimension-only radial mass used in the low-envelope frequency summation
of `app:ch_response:thm:response-literal-transfer`. -/
def lowEnvelopeRadialMass (n : ℕ) : ℝ :=
  ∫ η : Euclidean n, (1 + ‖η‖) ^ (-(n + 1 : ℝ))

/-- The radial mass in the complete-complement estimate is nonnegative. -/
theorem lowEnvelopeRadialMass_nonneg (n : ℕ) : 0 ≤ lowEnvelopeRadialMass n :=
  integral_nonneg (fun _ ↦ Real.rpow_nonneg (by positivity) _)

/-- Integrability of the radial majorant for the low-envelope estimate in
`app:ch_response:thm:response-literal-transfer`. -/
theorem integrable_lowEnvelope_radialMajorant {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun η : Euclidean n ↦ (ρ / (ρ + ‖η‖)) ^ (n + 1)) := by
  have he (η : Euclidean n) : (ρ / (ρ + ‖η‖)) ^ (n + 1) =
      ρ ^ (n + 1) * (ρ + ‖η‖) ^ (-(n + 1 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by simp,
      Real.rpow_natCast, div_pow, div_eq_mul_inv]
  simp_rw [he]
  exact (integrable_radialDecay (μ := volume) hρ (by simp)).const_mul _

/-- Exact radial mass after scaling, retaining the Lebesgue dimension factor
in `app:ch_response:thm:response-literal-transfer`. -/
theorem integral_lowEnvelope_radialMajorant {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ η : Euclidean n, (ρ / (ρ + ‖η‖)) ^ (n + 1)) =
      ρ ^ n * lowEnvelopeRadialMass n := by
  have he (η : Euclidean n) : (ρ / (ρ + ‖η‖)) ^ (n + 1) =
      ρ ^ (n + 1) * (ρ + ‖η‖) ^ (-(n + 1 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by simp,
      Real.rpow_natCast, div_pow, div_eq_mul_inv]
  simp_rw [he]
  rw [integral_const_mul, integral_radialDecay hρ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hρ]
  rw [show ((n + 1 : ℕ) : ℝ) + ((n : ℝ) - (n + 1)) = (n : ℝ) by
    push_cast; ring, Real.rpow_natCast]
  rfl

/-- Spending `s+n+1` additional source integrations leaves an integrable
majorant and a fixed polynomial loss, as required in the complete-complement
paragraph of `app:ch_response:thm:response-literal-transfer`. -/
theorem lowEnvelope_kernel_radialMajorant {n : ℕ} {L ρ : ℝ}
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hLρ : L ≤ ρ) (s q : ℕ) (η : Euclidean n) :
    (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1) ≤
      (ρ ^ s * (L / ρ) ^ q) * (ρ / (ρ + ‖η‖)) ^ (n + 1) := by
  let R := ρ + ‖η‖
  have hR : 0 < R := add_pos_of_pos_of_nonneg hρ (norm_nonneg η)
  have hρR : ρ ≤ R := le_add_of_nonneg_right (norm_nonneg η)
  have he : R ^ s * (L / R) ^ (q + s + n + 1) =
      L ^ s * (L / R) ^ q * (L / R) ^ (n + 1) := by
    rw [show q + s + n + 1 = s + q + (n + 1) by omega, pow_add, pow_add]
    simp only [div_pow]
    field_simp [hR.ne']
  change R ^ s * (L / R) ^ (q + s + n + 1) ≤ _
  rw [he]
  exact mul_le_mul
    (mul_le_mul (pow_le_pow_left₀ hL hLρ s)
      (pow_le_pow_left₀ (div_nonneg hL hR.le)
        (div_le_div_of_nonneg_left hL hρ hρR) q)
      (pow_nonneg (div_nonneg hL hR.le) q) (pow_nonneg hρ.le s))
    (pow_le_pow_left₀ (div_nonneg hL hR.le)
      (div_le_div_of_nonneg_right hLρ hR.le) (n + 1))
    (pow_nonneg (div_nonneg hL hR.le) (n + 1)) (by positivity)

/-- Full radial integration of the kernel profile in
`app:ch_response:thm:response-literal-transfer`. The loss `s+n` is fixed before
`q`, and no region of frequency space is removed. -/
theorem integral_lowEnvelope_kernel_profile_le {n : ℕ} {L ρ : ℝ}
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hLρ : L ≤ ρ) (s q : ℕ) :
    Integrable (fun η : Euclidean n ↦
      (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1)) ∧
    (∫ η : Euclidean n,
      (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1)) ≤
      lowEnvelopeRadialMass n * ρ ^ (s + n) * (L / ρ) ^ q := by
  have hi := (integrable_lowEnvelope_radialMajorant (n := n) hρ).const_mul
    (ρ ^ s * (L / ρ) ^ q)
  have hm : AEStronglyMeasurable (fun η : Euclidean n ↦
      (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1)) volume := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_const.add continuous_norm).pow s).mul
      ((continuous_const.div (continuous_const.add continuous_norm)
        (fun η ↦ (add_pos_of_pos_of_nonneg hρ (norm_nonneg η)).ne')).pow _)
  have hj : Integrable (fun η : Euclidean n ↦
      (ρ + ‖η‖) ^ s * (L / (ρ + ‖η‖)) ^ (q + s + n + 1)) := by
    apply hi.mono' hm
    filter_upwards [] with η
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact lowEnvelope_kernel_radialMajorant hL hρ hLρ s q η
  refine ⟨hj, (integral_mono hj hi (lowEnvelope_kernel_radialMajorant hL hρ hLρ s q)).trans_eq ?_⟩
  rw [integral_const_mul, integral_lowEnvelope_radialMajorant hρ, pow_add]
  ring

end JanetCartan.ResponseTransfer.LowEnvelope
