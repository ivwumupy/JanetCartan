module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.FiniteTemporal
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.MultiplierSlices

/-!
# Original multiplier-slice inversion from a finite symbol reserve

Pointwise Fourier inversion applies to the actual temporal integral because
it is continuous and integrable and its inverse is integrable on every spatial
slice. All three facts are proved from finite symbol bounds and the original
Schwartz test. Consumer: the literal fixed-time and retarded test actions in
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral KernelIdentification
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

private theorem physicalFourier_eq_of_integrable_inverse {n : ℕ}
    (g : Euclidean n → V) (hg : Continuous g) (hgi : Integrable g)
    (h : Euclidean n → V) (hi : Integrable h)
    (he : ∀ y, h y = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ η, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) • g η) (η : Euclidean n) :
    (∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • h y) = g η := by
  let G : Euclidean n → V := fun ξ ↦ g ((2 * Real.pi) • ξ)
  have hG : Continuous G := hg.comp (continuous_id.const_smul (2 * Real.pi))
  have hGi : Integrable G := hgi.comp_smul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hInv : 𝓕⁻ G = h := by
    funext y
    exact (fourierInv_physicalRescale_eq_integral g y).trans (he y).symm
  have hFourier : 𝓕 G = fun y ↦ h (-y) := by
    funext y
    have hh := congrFun hInv (-y)
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hh
  have hFG : Integrable (𝓕 G) := by rw [hFourier]; exact hi.comp_neg
  have hinversion := hG.fourier_fourierInv_eq hGi hFG
  rw [hInv] at hinversion
  have hη := congrFun hinversion ((2 * Real.pi)⁻¹ • η)
  change 𝓕 h ((2 * Real.pi)⁻¹ • η) = g ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • η)) at hη
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul, Real.fourier_eq'] at hη
  convert hη using 1
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [real_inner_smul_right]
  congr 2
  have hp : -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ y η) = -inner ℝ y η := by
    field_simp
  rw [hp, mul_comm]

/-- The spatial Fourier transform of the actual original multiplier slice is
the literal temporal inverse, with `(2π)⁻¹` unchanged. Only `d+2` bounded
symbol derivatives are used. The two integrability inputs and continuity of
pointwise Fourier inversion are proved in `FiniteFourier` and `FiniteTemporal`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalFourier_physicalMultiplierIntegral_spatialSlice
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (C : ℕ → ℝ)
    (hbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k)
    (s : ℝ) (η : Euclidean d) :
    (∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) •
      physicalMultiplierIntegral β v (timeSpacePoint s y)) =
      cutTemporalFourierSlice β (fun _ ↦ 1) v s η := by
  have hb0 (ξ : E) : ‖β ξ‖ ≤ C 0 := by
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 (by omega) ξ
  exact physicalFourier_eq_of_integrable_inverse
    (cutTemporalFourierSlice β (fun _ ↦ 1) v s)
    (continuous_uncutTemporalFourierSlice_of_bound β hβ.continuous v (C 0) hb0 s)
    (integrable_uncutTemporalFourierSlice_of_bound β hβ.continuous v (C 0) hb0 s)
    (fun y ↦ physicalMultiplierIntegral β v (timeSpacePoint s y))
    (integrable_physicalMultiplierIntegral_spatialSlice β hβ v C hbound s)
    (physicalMultiplierIntegral_eq_spatialInverse β hβ.continuous v (C 0) hb0 s) η

private theorem graphOperator_eq_integrable_sourceFourier {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin q) (Fin q) ℂ)
    (u : Euclidean n → V) (hu : Integrable u) (x : Euclidean n) :
    graphOperator S (fun z _ η ↦ A z η) u x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η,
        Complex.exp (Complex.I * (S x η : ℂ)) • (A x η).mulVec
          (∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y) := by
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  have hi : Integrable (fun y ↦
      Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y) := by
    apply hu.norm.mono'
    · exact (by fun_prop : Continuous (fun y : Euclidean n ↦
        Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)))).aestronglyMeasurable.smul
          hu.aestronglyMeasurable
    · filter_upwards [] with y
      simp only [norm_smul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hL := (sourceMatrixAction (A x η)).integral_comp_comm hi
  change (∫ y, (A x η).mulVec
    (Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y)) =
    (A x η).mulVec (∫ y, Complex.exp (Complex.I * (-(inner ℝ y η) : ℝ)) • u y) at hL
  rw [← hL, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Matrix.mulVec_smul, smul_smul, ← Complex.exp_add]
  congr 2
  simp only [graphOscillation, Complex.ofReal_sub, Complex.ofReal_neg]
  congr 1
  ring

/-- The original spatial graph acts on the actual multiplier slice, without
asserting that finite budgets make that slice Schwartz. This is the literal
`U_b(t,s)(Bβv)(s)` of `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem uncutFixedTimeFourier_eq_graphOperator_of_finite_bounds
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (C : ℕ → ℝ)
    (hbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k)
    (t s : ℝ) (y : Euclidean d) :
    cutFixedTimeFourier Ψ b β (fun _ ↦ 1) v t s y =
      graphOperator (Ψ t s) (fun y _ η ↦ b t s y η)
        (fun z ↦ physicalMultiplierIntegral β v (timeSpacePoint s z)) y := by
  rw [graphOperator_eq_integrable_sourceFourier _ _ _
    (integrable_physicalMultiplierIntegral_spatialSlice β hβ v C hbound s)]
  simp_rw [physicalFourier_physicalMultiplierIntegral_spatialSlice β hβ v C hbound]
  rfl

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
