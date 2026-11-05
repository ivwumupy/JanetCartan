module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Coordinates
public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Derivatives

/-!
# Unitary normalization of the initial inverse Fourier integral

For `app:ch_background:prop:bg-adjoint` the transverse dimension is `n - 1`
and the measure is Lebesgue measure. The unitary radian inverse has prefactor
`(2π)^(-(n-1)/2)`. `RawInputRealization.field` has no prefactor, so its value
is `(2π)^((n-1)/2)` times this unitary integral. These statements hold for
ordinary integrals; constructing the partial operator on all carrier L²
classes is a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform

namespace JanetCartan.CarrierSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Conversion factor from unitary radian synthesis to the unprefactored
synthesis in `app:ch_waves:eq:individual-representation`. -/
def synthesisFactor (n : ℕ) : ℝ := Real.sqrt ((2 * Real.pi) ^ (n - 1))

/-- The conversion factor is strictly positive, also in transverse dimension
zero (`app:ch_background:prop:bg-adjoint`). -/
theorem synthesisFactor_pos (n : ℕ) : 0 < synthesisFactor n := by
  unfold synthesisFactor
  positivity

/-- Exact half-dimensional `2π` factor
(`app:ch_background:prop:bg-adjoint`). -/
theorem synthesisFactor_eq_rpow (n : ℕ) :
    synthesisFactor n = (2 * Real.pi) ^ ((n - 1 : ℕ) / (2 : ℝ)) := by
  rw [synthesisFactor, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Squared conversion factor is the physical-frequency Jacobian
(`app:ch_background:prop:bg-adjoint`). -/
theorem synthesisFactor_sq (n : ℕ) :
    synthesisFactor n ^ 2 = (2 * Real.pi) ^ (n - 1) :=
  Real.sq_sqrt (by positivity)

/-- The unprefactored radian inverse integral on the actual transverse
Euclidean space (`app:ch_background:prop:bg-adjoint`). -/
def radianInverseIntegral (f : Euclidean (n - 1) → F) (y : Euclidean (n - 1)) : F :=
  ∫ η, Complex.exp ((inner ℝ η y : ℂ) * Complex.I) • f η

/-- The normalized inverse integral used for the initial-variable L²
identification (`app:ch_background:prop:bg-adjoint`). -/
def unitaryInverseIntegral (f : Euclidean (n - 1) → F) (y : Euclidean (n - 1)) : F :=
  (synthesisFactor n)⁻¹ • radianInverseIntegral f y

omit [CompleteSpace F] in
/-- The inverse kernel is the physical forward kernel at the negative
covector (`app:ch_background:prop:bg-adjoint`). -/
theorem radianInverseIntegral_eq_physical (f : Euclidean (n - 1) → F)
    (y : Euclidean (n - 1)) :
    radianInverseIntegral f y = Localization.physicalFourierIntegral volume f
      (InnerProductSpace.toDual ℝ (Euclidean (n - 1)) (-y)) := by
  simp only [radianInverseIntegral, Localization.physicalFourierIntegral,
    Localization.phaseOscillation, InnerProductSpace.toDual_apply_apply,
    inner_neg_left, neg_neg, real_inner_comm y]

omit [CompleteSpace F] in
/-- Exact argument rescaling to Mathlib's inverse transform; no L¹ hypothesis
is needed for this identity of Bochner integrals
(`app:ch_background:prop:bg-adjoint`). -/
theorem radianInverseIntegral_eq_fourierInv (f : Euclidean (n - 1) → F)
    (y : Euclidean (n - 1)) :
    radianInverseIntegral f y = 𝓕⁻ f ((2 * Real.pi)⁻¹ • y) := by
  rw [Real.fourierInv_eq', radianInverseIntegral]
  congr 1
  funext η
  congr 2
  rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The unprefactored inverse integral of L¹ ∩ L² data has finite L² energy
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_norm_sq_radianInverseIntegral {f : Euclidean (n - 1) → F}
    (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    Integrable (fun y ↦ ‖radianInverseIntegral f y‖ ^ 2) := by
  simp_rw [radianInverseIntegral_eq_physical]
  exact (Localization.integrable_norm_sq_physicalFourierIntegral h₁
    (h₂.integrable_norm_pow (by decide))).comp_neg

/-- Physical inverse Plancherel with its exact Jacobian
(`app:ch_background:prop:bg-adjoint`). -/
theorem integral_norm_sq_radianInverseIntegral {f : Euclidean (n - 1) → F}
    (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    (∫ y, ‖radianInverseIntegral f y‖ ^ 2) =
      synthesisFactor n ^ 2 * ∫ η, ‖f η‖ ^ 2 := by
  simp_rw [radianInverseIntegral_eq_physical]
  rw [integral_neg_eq_self (fun y : Euclidean (n - 1) ↦
    ‖Localization.physicalFourierIntegral volume f
      (InnerProductSpace.toDual ℝ (Euclidean (n - 1)) y)‖ ^ 2)]
  simpa [synthesisFactor_sq] using
    Localization.integral_norm_sq_physicalFourierIntegral h₁
      (h₂.integrable_norm_pow (by decide))

/-- Normalized synthesis has finite L² energy
(`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_norm_sq_unitaryInverseIntegral {f : Euclidean (n - 1) → F}
    (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    Integrable (fun y ↦ ‖unitaryInverseIntegral f y‖ ^ 2) := by
  simp only [unitaryInverseIntegral, norm_smul, mul_pow]
  exact (integrable_norm_sq_radianInverseIntegral h₁ h₂).const_mul _

/-- Unitary radian Plancherel on ordinary L¹ ∩ L² data, including compact
smooth tests (`app:ch_background:prop:bg-adjoint`). -/
theorem integral_norm_sq_unitaryInverseIntegral {f : Euclidean (n - 1) → F}
    (h₁ : Integrable f) (h₂ : MemLp f 2 volume) :
    (∫ y, ‖unitaryInverseIntegral f y‖ ^ 2) = ∫ η, ‖f η‖ ^ 2 := by
  simp only [unitaryInverseIntegral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (synthesisFactor_pos n)), mul_pow, integral_const_mul]
  rw [integral_norm_sq_radianInverseIntegral h₁ h₂]
  field_simp [ne_of_gt (synthesisFactor_pos n)]

/-- The exact constant converting the unitary inverse into
`RawInputRealization.field`, whose density already uses synthesis normalization
(`app:ch_waves:eq:individual-representation`; `app:ch_background:prop:bg-adjoint`). -/
theorem rawField_eq_synthesisFactor_smul {ι : Type*} [Fintype ι] {radius : ι → ℝ}
    (β : ι → Euclidean (n - 1) → ℂ) (v : RawInputRealization.Input n radius)
    (y : Euclidean (n - 1)) :
    RawInputRealization.field β v y =
      synthesisFactor n • unitaryInverseIntegral (RawInputRealization.density β v) y := by
  rw [unitaryInverseIntegral, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (synthesisFactor_pos n)), one_smul]
  exact RawInputRealization.field_eq_integral_exp β v y

end JanetCartan.CarrierSobolev
