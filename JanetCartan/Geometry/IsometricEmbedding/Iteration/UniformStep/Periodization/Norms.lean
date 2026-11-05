module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Derivatives

/-!
# Sobolev transfer for the same cut correction fields

For `main:eq:joint-physical-profile`, the physical norm is the existing Cartesian
jet norm with Lebesgue measure. Periodization preserves the derivative energy
exactly; the Fourier norm comparison costs only the existing `sqrt (m!)` factor.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.UniformStep.Periodization

open LocalSobolev AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {r : ℝ} {f : Euclidean n → Euclidean N}

/-- Cartesian derivatives of the actual periodization are the physical
Cartesian derivatives at the centered representative (`main:eq:joint-physical-profile`). -/
theorem multiindexDeriv_vectorPeriodization (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) (z : Torus n) :
    periodicMultiindexDeriv α (vectorPeriodization f) z =
      cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α
        (centeredTorusRepresentative z) := by
  calc
    _ = cartesianJetDerivative
        (fun j ↦ iteratedFDeriv ℝ j (periodicLift (vectorPeriodization f))) α
        (centeredTorusRepresentative z) := by
      rw [AuxiliaryRawBand.cartesianJetDerivative_periodicLift
        (isSmoothPeriodic_vectorPeriodization hr hs hf)]
      simp [periodicLift]
    _ = _ := by
      unfold cartesianJetDerivative
      dsimp only
      rw [iteratedFDeriv_vectorPeriodization_eq hr hs _ (centeredTorusRepresentative_mem z)]

/-- The physical Cartesian derivatives still vanish outside the same cell
(`main:eq:joint-physical-profile`); differentiation introduces no support loss. -/
theorem cartesianJetDerivative_eq_zero_outside_cell (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (α : Fin n → ℕ)
    {x : Euclidean n} (hx : x ∉ halfOpenCell n) :
    cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x = 0 := by
  have hjet : iteratedFDeriv ℝ (sobolevDerivativeList α).length f x = 0 := by
    by_contra h
    exact hx (support_subset_halfOpenCell hr
      ((tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (sobolevDerivativeList α).length).trans hs) h)
  simp [cartesianJetDerivative, hjet]

/-- Exact L² energy transfer for each Cartesian derivative in
`main:eq:joint-physical-profile`. -/
theorem integral_multiindexDeriv_vectorPeriodization_sq (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) :
    (∫ z, ‖periodicMultiindexDeriv α (vectorPeriodization f) z‖ ^ 2) =
      ∫ x, ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x‖ ^ 2 := by
  simp_rw [multiindexDeriv_vectorPeriodization hr hs hf α]
  rw [integral_representative
    (fun x ↦ ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x‖ ^ 2)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [cartesianJetDerivative_eq_zero_outside_cell hr hs α hx]

/-- Exact identification with the shared whole-space Cartesian Sobolev norm
of the same physical field (`main:eq:joint-physical-profile`). -/
theorem periodicDerivativeL2Norm_vectorPeriodization (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    periodicDerivativeL2Norm m (vectorPeriodization f) =
      cartesianJetNorm univ m (fun j ↦ iteratedFDeriv ℝ j f) := by
  unfold periodicDerivativeL2Norm cartesianJetNorm cartesianJetEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),
    integral_multiindexDeriv_vectorPeriodization_sq hr hs hf]
  simp

/-- Integer Fourier Sobolev transfer consumed by `StageConstants.ComponentEstimates`.
Every bound concerns the same cut field; no torus estimate is assumed
(`main:eq:joint-physical-profile`). -/
theorem periodicSobolevNorm_vectorPeriodization_le (hr : r < 1 / 2)
    (hs : tsupport f ⊆ {x | ∀ i, |x i| ≤ r}) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    periodicSobolevNorm m (vectorPeriodization f) ≤
      Real.sqrt (m.factorial : ℝ) *
        cartesianJetNorm univ m (fun j ↦ iteratedFDeriv ℝ j f) := by
  simpa only [periodicDerivativeL2Norm_vectorPeriodization hr hs hf] using
    periodicSobolevNorm_le_factorial_mul_derivativeL2Norm
      (isSmoothPeriodic_vectorPeriodization hr hs hf) m

end JanetCartan.UniformStep.Periodization
