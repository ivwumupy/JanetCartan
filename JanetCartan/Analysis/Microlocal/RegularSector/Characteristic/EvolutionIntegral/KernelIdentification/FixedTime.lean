module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.FourierSplitting
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.TimeSpace

/-!
# Fixed-time Fourier kernels with compact frequency support

Absolute integrability and the measure-preserving time/space split give the
fixed-time spectral formula in
`app:ch_regular_base:eq:fixed-time-representation`. The temporal inverse Fourier
integral carries `(2π)⁻¹`; the spatial evolution carries `(2π)⁻ᵈ`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The temporal inverse Fourier integrand at a fixed spatial covector.
The Schwartz datum has already been multiplied by the source mask.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutTemporalFourierIntegrand (β θ : E → ℂ) (v : SchwartzMap E V)
    (s : ℝ) (η : Euclidean d) (τ : ℝ) : V :=
  Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) •
    ((θ (timeSpacePoint τ η) * β (timeSpacePoint τ η)) •
      sourceInputFourierTransform v (timeSpacePoint τ η))

/-- The partially inverted Fourier multiplier, with the one-dimensional
physical normalization in `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutTemporalFourierSlice (β θ : E → ℂ) (v : SchwartzMap E V)
    (s : ℝ) (η : Euclidean d) : V :=
  ((2 * Real.pi : ℂ)⁻¹) • ∫ τ, cutTemporalFourierIntegrand β θ v s η τ

/-- The spatial spectral evolution at fixed times. Identifying the temporal
slice with the spatial Fourier transform of the actual multiplier is a further
Fourier-inversion step. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
def cutFixedTimeFourier (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β θ : E → ℂ) (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d) : V :=
  ((2 * Real.pi) ^ d : ℂ)⁻¹ • ∫ η,
    Complex.exp (Complex.I * (Ψ t s y η : ℂ)) •
      (b t s y η).mulVec (cutTemporalFourierSlice β θ v s η)

/-- The full spacetime covector integrand before the genuine Fubini split.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutFixedTimeFourierIntegrand (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (β θ : E → ℂ) (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d) (ξ : E) : V :=
  Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)) •
    (Complex.exp (Complex.I * (Ψ t s y (spatialPart ξ) : ℂ)) •
      (b t s y (spatialPart ξ)).mulVec ((θ ξ * β ξ) • sourceInputFourierTransform v ξ))

/-- Compact covector support supplies absolute integrability on each temporal
fiber; no Fourier splitting is assumed. Consumer: `integral_cutFixedTimeFourier`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_cutTemporalFourierIntegrand (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ)
    (s : ℝ) (η : Euclidean d) : Integrable (cutTemporalFourierIntegrand β θ v s η) := by
  have hp : Continuous (fun τ ↦ timeSpacePoint τ η) :=
    continuous_timeSpacePoint.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous (cutTemporalFourierIntegrand β θ v s η) := by
    unfold cutTemporalFourierIntegrand
    exact (show Continuous (fun τ : ℝ ↦ Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)))
      by fun_prop).smul (((hθ.comp hp).mul (hβ.comp hp)).smul
      ((sourceInputFourierTransform v).continuous.comp hp))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    (hθcs.image (show Continuous (fun ξ : E ↦ ξ 0) by fun_prop))
  intro τ hτ
  have hz : timeSpacePoint τ η ∉ tsupport θ := fun h ↦
    hτ ⟨timeSpacePoint τ η, h, timeSpacePoint_time τ η⟩
  simp [cutTemporalFourierIntegrand, image_eq_zero_of_notMem_tsupport hz]

/-- The finite spacetime-frequency kernel is absolutely integrable from
primitive continuity and the actual compact frequency cutoff. Consumer:
`integral_cutFixedTimeFourier`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_cutFixedTimeFourierIntegrand
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d)
    (hΨ : Continuous (Ψ t s y)) (hb : Continuous (b t s y))
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    Integrable (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) := by
  have hc : Continuous (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) := by
    have hp := hΨ.comp continuous_spatialPart
    have ha := hb.comp continuous_spatialPart
    unfold cutFixedTimeFourierIntegrand
    exact (show Continuous (fun ξ : E ↦ Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ)))
      by fun_prop).smul
      ((continuous_const.mul (Complex.continuous_ofReal.comp hp)).cexp.smul
        (ha.matrix_mulVec ((hθ.mul hβ).smul (sourceInputFourierTransform v).continuous)))
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hθcs (fun ξ hξ ↦ by
      simp [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hξ]))

/-- Actual Fubini and matrix-integral interchange give the fixed-time spectral
representation, with `(2π)⁻⁽ᵈ⁺¹⁾ = (2π)⁻ᵈ (2π)⁻¹`. Consumer: the finite-cutoff
fixed-`r` identity in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_cutFixedTimeFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d)
    (hΨ : Continuous (Ψ t s y)) (hb : Continuous (b t s y))
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
      (∫ ξ, cutFixedTimeFourierIntegrand Ψ b β θ v t s y ξ) =
      cutFixedTimeFourier Ψ b β θ v t s y := by
  rw [integral_eq_space_time _
    (integrable_cutFixedTimeFourierIntegrand Ψ b β θ v t s y hΨ hb hβ hθ hθcs)]
  have he (η : Euclidean d) :
      (∫ τ, cutFixedTimeFourierIntegrand Ψ b β θ v t s y (timeSpacePoint τ η)) =
      Complex.exp (Complex.I * (Ψ t s y η : ℂ)) •
        (b t s y η).mulVec (∫ τ, cutTemporalFourierIntegrand β θ v s η τ) := by
    have hi := integrable_cutTemporalFourierIntegrand β θ v hβ hθ hθcs s η
    have hL := (sourceMatrixAction (b t s y η)).integral_comp_comm hi
    change (∫ τ, (b t s y η).mulVec (cutTemporalFourierIntegrand β θ v s η τ)) =
      (b t s y η).mulVec (∫ τ, cutTemporalFourierIntegrand β θ v s η τ) at hL
    rw [← hL, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with τ
    simp only [cutFixedTimeFourierIntegrand, timeSpacePoint_time, spatialPart_timeSpacePoint,
      cutTemporalFourierIntegrand, Matrix.mulVec_smul]
    exact smul_comm _ _ _
  simp_rw [he]
  unfold cutFixedTimeFourier cutTemporalFourierSlice
  simp only [Matrix.mulVec_smul]
  simp_rw [smul_comm _ ((2 * Real.pi : ℂ)⁻¹), integral_smul, smul_smul]
  congr 1
  rw [pow_succ, mul_inv_rev]
  exact mul_comm _ _

/-- The actual compact-frequency graph equals the fixed-time spatial spectral
operator applied to the temporally inverted multiplier, with the source and
output masks in the prescribed order. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cut_elapsedGraph_eq_fixedTimeFourier
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (hΨ : Continuous (Ψ (x 0) (x 0 - r) (spatialPart x)))
    (hb : Continuous (b (x 0) (x 0 - r) (spatialPart x)))
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x =
      χout x • cutFixedTimeFourier Ψ b β θ
        (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
        (x 0) (x 0 - r) (spatialPart x) := by
  rw [cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β θ hs r u x]
  exact congrArg (χout x • ·)
    (integral_cutFixedTimeFourier Ψ b β θ _ _ _ _ hΨ hb hβ hθ hθcs)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
