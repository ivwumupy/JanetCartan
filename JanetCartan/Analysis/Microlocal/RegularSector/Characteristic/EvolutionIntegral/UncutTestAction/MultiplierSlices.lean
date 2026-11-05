module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.TemporalIntegral

/-!
# The original uncut multiplier-slice Fourier identity

Spatial Fourier inversion identifies the actual uncut multiplier slice with
the temporal integral. All integrability, continuity, and Schwartz properties
used by inversion are proved from the original Schwartz frequency datum.
Source: `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The physical-to-cycle Fourier rescaling for ordinary function-valued
inversion, retaining `(2π)⁻ⁿ` in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem fourierInv_physicalRescale_eq_integral {n : ℕ}
    (g : Euclidean n → V) (y : Euclidean n) :
    𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ η, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • g η := by
  rw [Real.fourierInv_eq']
  have hphase (ξ : Euclidean n) :
      Complex.exp ((2 * Real.pi * inner ℝ ξ y : ℝ) * Complex.I) =
        Complex.exp (Complex.I * (inner ℝ y ((2 * Real.pi) • ξ) : ℂ)) := by
    rw [real_inner_smul_right, real_inner_comm y ξ]
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  change (∫ ξ : Euclidean n,
    (fun η ↦ Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • g η)
      ((2 * Real.pi) • ξ)) = _
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun η : Euclidean n ↦ Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • g η)
    (2 * Real.pi) (hR := by positivity)]
  simp only [Euclidean, finrank_euclideanSpace_fin]
  norm_cast

private theorem sourceFourier_eq_of_inverse_integral {n : ℕ}
    (g : Euclidean n → V) (hg : Continuous g) (hgi : Integrable g)
    (h : SchwartzMap (Euclidean n) V)
    (he : ∀ y, h y = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ η, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • g η) (η : Euclidean n) :
    sourceInputFourierTransform h η = g η := by
  let G : Euclidean n → V := fun ξ ↦ g ((2 * Real.pi) • ξ)
  have hG : Continuous G := hg.comp (continuous_id.const_smul (2 * Real.pi))
  have hGi : Integrable G := hgi.comp_smul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hInv : 𝓕⁻ G = (h : Euclidean n → V) := by
    funext y
    exact (fourierInv_physicalRescale_eq_integral g y).trans (he y).symm
  have hFourier : 𝓕 G = fun y ↦ h (-y) := by
    funext y
    have hh := congrFun hInv (-y)
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hh
  have hFG : Integrable (𝓕 G) := by
    rw [hFourier]
    exact h.integrable.comp_neg
  have hinversion := hG.fourier_fourierInv_eq hGi hFG
  rw [hInv] at hinversion
  have hη := congrFun hinversion ((2 * Real.pi)⁻¹ • η)
  change sourceInputFourierTransform h η = g ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • η)) at hη
  simpa only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    one_smul] using hη

/-- The spatial transform of the actual inverse-Fourier slice is the
temporal inverse of the same uncut frequency datum. Continuity and both
integrability requirements of Fourier inversion are discharged above.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_spatialSlice_physicalInverse
    (f : SchwartzMap E V) (s : ℝ) (η : Euclidean d) :
    sourceInputFourierTransform (spatialSchwartzSlice (physicalInverseSchwartz f) s) η =
      physicalTemporalIntegral f s η := by
  exact sourceFourier_eq_of_inverse_integral (physicalTemporalIntegral f s)
    (continuous_physicalTemporalIntegral f s) (integrable_physicalTemporalIntegral f s)
    (spatialSchwartzSlice (physicalInverseSchwartz f) s)
    (physicalInverseSchwartz_eq_temporalIntegral f s) η

/-- The actual uncut multiplier slice has exactly the literal temporal
Fourier integral of `β` times the source-masked Fourier datum. The argument
`1` denotes absence of a frequency cutoff in the existing integral definition.
Consumer: the uncut fixed-`r` spatial graph in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem sourceInputFourierTransform_physicalMultiplierSlice
    (β : E → ℂ) (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V)
    (s : ℝ) (η : Euclidean d) :
    sourceInputFourierTransform (physicalMultiplierSlice β v s) η =
      cutTemporalFourierSlice β (fun _ ↦ 1) v s η := by
  rw [physicalMultiplierSlice, physicalMultiplier_eq_physicalInverse β hβ,
    sourceInputFourierTransform_spatialSlice_physicalInverse]
  simp only [physicalTemporalIntegral, cutTemporalFourierSlice,
    cutTemporalFourierIntegrand, one_mul, SchwartzMap.smulLeftCLM_apply_apply hβ]

/-- The uncut spectral fixed-time evolution equals the original spatial
graph applied to the actual multiplier slice. No growth or convergence of the
graph is assumed to establish this exact integral identity. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem uncutFixedTimeFourier_eq_graphOperator
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β : E → ℂ) (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V)
    (t s : ℝ) (y : Euclidean d) :
    cutFixedTimeFourier Ψ b β (fun _ ↦ 1) v t s y =
      graphOperator (Ψ t s) (fun y _ η ↦ b t s y η)
        (physicalMultiplierSlice β v s) y := by
  rw [graphOperator_eq_sourceFourierIntegral]
  simp_rw [sourceInputFourierTransform_physicalMultiplierSlice β hβ]
  rfl

/-- The physical cutoff is a scalar factor of the original uncut frequency
integrand. Consumer: dominated convergence for both finite-budget and Schwartz
variants of `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cutFixedTimeFourierIntegrand_eq_frequency_smul
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d) (ξ : E) :
    cutFixedTimeFourierIntegrand Ψ b β θ v t s y ξ =
      θ ξ • cutFixedTimeFourierIntegrand Ψ b β (fun _ ↦ 1) v t s y ξ := by
  simp only [cutFixedTimeFourierIntegrand, one_mul, mul_smul, Matrix.mulVec_smul]
  rw [smul_comm _ (θ ξ), smul_comm _ (θ ξ)]


end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
