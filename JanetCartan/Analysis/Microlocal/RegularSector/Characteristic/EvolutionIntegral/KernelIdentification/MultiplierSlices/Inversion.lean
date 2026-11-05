module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.SchwartzInput

/-!
# Physical inverse Fourier transform for the multiplier slices

The full multiplier and its spatial slices in
`app:ch_regular_base:eq:fixed-time-representation` use this inverse of the
existing unnormalized `sourceInputFourierTransform`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral
variable {n q : ℕ}

/-- Inverse Fourier transform in physical covectors, used to construct the
full multiplier and its spatial slices in
`app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalInverseSchwartz (f : SchwartzMap (Euclidean n) (Fin q → ℂ)) :
    SchwartzMap (Euclidean n) (Fin q → ℂ) :=
  𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean n)
      (Units.mk0 (2 * Real.pi) (by positivity))) f)

/-- Actual Fourier inversion, with the existing unnormalized physical
transform. Consumer: the spatial slice identity in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_physicalInverseSchwartz
    (f : SchwartzMap (Euclidean n) (Fin q → ℂ)) :
    sourceInputFourierTransform (physicalInverseSchwartz f) = f := by
  apply SchwartzMap.ext
  intro η
  unfold sourceInputFourierTransform physicalInverseSchwartz
  rw [fourier_fourierInv_eq]
  change f ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • η)) = f η
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The constructed inverse has precisely the physical integral and
`(2π)⁻ⁿ` normalization. Consumer: identification of the full multiplier
and its spatial slices in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalInverseSchwartz_eq_integral
    (f : SchwartzMap (Euclidean n) (Fin q → ℂ)) (x : Euclidean n) :
    physicalInverseSchwartz f x = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • f ξ := by
  unfold physicalInverseSchwartz
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  have hphase (ξ : Euclidean n) :
      Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I) =
        Complex.exp (Complex.I * (inner ℝ x ((2 * Real.pi) • ξ) : ℂ)) := by
    rw [real_inner_smul_right, real_inner_comm x ξ]
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  change (∫ ξ : Euclidean n,
    (fun η ↦ Complex.exp (Complex.I * (inner ℝ x η : ℂ)) • f η)
      ((2 * Real.pi) • ξ)) = _
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun ξ : Euclidean n ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • f ξ) (2 * Real.pi)
    (hR := by positivity)]
  simp only [Euclidean, finrank_euclideanSpace_fin]
  norm_cast

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
