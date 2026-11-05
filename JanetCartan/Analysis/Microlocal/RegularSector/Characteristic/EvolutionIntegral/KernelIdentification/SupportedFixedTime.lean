module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.MultiplierSlices
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedElapsed
/-!
# Fixed-time physical identity from supported regularity

The primitive phase is required to be continuous only on the multiplier's
frequency support, where the full kernel can be nonzero. This supplies actual
integrability before the time/space Fubini split. Source:
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral FourierIntegral.LowBounds.FrequencyCutoff
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ
/-- Fubini for an integrable compact spectral kernel. Consumer:
`cut_elapsedGraph_eq_spatialGraph_of_support`, which proves this integrability
from supported regularity in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integral_cutFixedTimeFourier_of_integrable
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d)
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    Integrable (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) →
    ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
      (∫ ξ, cutFixedTimeFourierIntegrand Ψ b β θ v t s y ξ) =
      cutFixedTimeFourier Ψ b β θ v t s y := by
  intro hi
  rw [integral_eq_space_time _ hi]
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

/-- Supported primitive continuity and the actual compact frequency cutoff
supply absolute integrability of the finite kernel. Consumer: the supported
fixed-time identity in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_cutFixedTimeFourierIntegrand_of_support
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E V) (t s : ℝ) (y : Euclidean d)
    (hΨ : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ t s y (spatialPart ξ)) ξ)
    (hb : ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b t s y (spatialPart ξ)) ξ)
    (hβ : Continuous β) (hθ : Continuous θ) (hθcs : HasCompactSupport θ) :
    Integrable (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) := by
  have hsupport : tsupport (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) ⊆ tsupport β := by
    apply closure_minimal _ (isClosed_tsupport β)
    intro ξ hξ
    by_contra hn
    exact hξ (by simp [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hn])
  have hc : Continuous (cutFixedTimeFourierIntegrand Ψ b β θ v t s y) := by
    apply continuous_of_tsupport
    intro ξ hξ
    have hmem := hsupport hξ
    have hmv : ContinuousAt (fun ξ : E ↦ (b t s y (spatialPart ξ)).mulVec
        ((θ ξ * β ξ) • sourceInputFourierTransform v ξ)) ξ := by
      have hcont : Continuous (fun p : Matrix (Fin q) (Fin q) ℂ × V ↦ p.1.mulVec p.2) :=
        continuous_fst.matrix_mulVec continuous_snd
      exact hcont.continuousAt.comp ((hb ξ hmem).prodMk
        ((hθ.mul hβ).continuousAt.smul (sourceInputFourierTransform v).continuous.continuousAt))
    unfold cutFixedTimeFourierIntegrand
    exact (show ContinuousAt (fun ξ : E ↦ Complex.exp (Complex.I * ((s * ξ 0 : ℝ) : ℂ))) ξ
      by fun_prop).smul
      ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (hΨ ξ hmem))).cexp.smul hmv)
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hθcs (fun ξ hξ ↦ by
      simp [cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hξ]))

/-- The literal fixed-`r` identity with regularity required only on the
physical and conic supports. The source mask precedes the actual multiplier,
whose slice is followed by the spatial evolution and output mask. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem cut_elapsedGraph_eq_spatialGraph_of_support
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β θ : E → ℂ)
    (hs : ContDiff ℝ ∞ χsource) (r : ℝ) (u : graphTestSpace (d + 1) q) (x : E)
    (hΨ : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ Ψ (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (hb : x ∈ tsupport χout → ∀ ξ ∈ tsupport β,
      ContinuousAt (fun ξ : E ↦ b (x 0) (x 0 - r) (spatialPart x) (spatialPart ξ)) ξ)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ) :
    graphOperator (elapsedPhase Ψ r)
      (frequencyCutFullAmplitude θ (elapsedAmplitude b χout χsource β r))
      (fun z ↦ (u.val z).ofLp) x =
      χout x • graphOperator (Ψ (x 0) (x 0 - r))
        (fun y _ η ↦ b (x 0) (x 0 - r) y η)
        (cutPhysicalMultiplierSlice β θ
          (graphTestToSchwartz (complexSourceMaskTest χsource hs u))
          hβ hθ hθcs (x 0 - r)) (spatialPart x) := by
  rw [cut_elapsedGraph_eq_sourceFourierIntegral Ψ b χout χsource β θ hs r u x]
  by_cases hx : χout x = 0
  · simp [hx]
  · rw [← cutFixedTimeFourier_eq_graphOperator Ψ b β θ _ hβ hθ hθcs]
    apply congrArg (χout x • ·)
    apply integral_cutFixedTimeFourier_of_integrable Ψ b β θ _ _ _ _
      hβ.continuous hθ.continuous hθcs
    exact integrable_cutFixedTimeFourierIntegrand_of_support Ψ b β θ _ _ _ _
      (hΨ (subset_tsupport χout hx)) (hb (subset_tsupport χout hx))
      hβ.continuous hθ.continuous hθcs

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
