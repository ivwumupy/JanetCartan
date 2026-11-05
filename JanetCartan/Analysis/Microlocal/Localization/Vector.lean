module
public import JanetCartan.Analysis.Microlocal.Localization.Coefficients
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Vector-valued nonstationary integration

The finite-dimensional amplitude in `app:ch_osc:prop:osc-source-shell` is
handled by norm-one complex linear functionals. The result holds in any complex
Banach space, hence also for the chosen finite-dimensional Frobenius norm,
without a dimension loss. Compact support supplies Bochner integrability.
-/

open scoped ContDiff
open MeasureTheory
@[expose] public noncomputable section
namespace JanetCartan.Localization
variable {E ι F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure]
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- `app:ch_osc:prop:osc-source-shell`: Local smoothness and compact amplitude support make the vector-valued oscillatory integrand integrable. -/
theorem integrable_phaseOscillation_smul {U : Set E} (hU : IsOpen U)
    (ψ : E → ℝ) (a : E → F) (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ U) (hc : HasCompactSupport a) :
    Integrable (fun x ↦ phaseOscillation ψ x • a x) μ := by
  have hf : ContDiffOn ℝ ∞ (phaseOscillation ψ) U :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hψ).mul contDiffOn_const).cexp
  exact (contDiff_of_contDiffOn_support_neighborhood hU (hf.smul ha)
    ((tsupport_smul_subset_right _ _).trans hs)).continuous.integrable_of_hasCompactSupport hc.smul_left

/-- `app:ch_osc:prop:osc-source-shell`: The repeated integration-by-parts bound for complex Banach-valued amplitudes, with the same explicit constants as the scalar estimate. -/
theorem norm_vector_oscillatory_integral_le {U : Set E} (hU : IsOpen U)
    (e : ι → E) (ψ : E → ℝ) (a : E → F) (q : ℕ)
    (hψ : ContDiffOn ℝ ∞ ψ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    {δ G A L R : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hR : 0 < R)
    (hgap : ∀ x ∈ U, δ * R ^ 2 ≤ phaseGradientSquare e ψ x)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ ψ x‖ ≤ G * R)
    {P C : ℕ → ℝ} (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ x ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) ψ x‖ ≤ P j * R * L ^ j)
    (ha_bound : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖∫ x, phaseOscillation ψ x • a x ∂μ‖ ≤
      (transposeDerivativeConstant e (phaseCoefficientDerivativeBound e δ G P) C q 0 *
        (A * (L / R) ^ q)) * μ.real (tsupport a) := by
  obtain ⟨g, hg, hv⟩ := exists_dual_vector'' ℂ (∫ x, phaseOscillation ψ x • a x ∂μ)
  have hsupport : tsupport (g ∘ a) ⊆ tsupport a := tsupport_comp_subset g.map_zero a
  have hga : ContDiffOn ℝ ∞ (g ∘ a) U :=
    (g.restrictScalars ℝ).contDiff.comp_contDiffOn ha
  have hgc : HasCompactSupport (g ∘ a) := hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hgan : ∀ x ∈ tsupport (g ∘ a), ∀ r,
      ‖iteratedFDeriv ℝ r (g ∘ a) x‖ ≤ C r * (A * L ^ r) := by
    intro x hx r
    apply ((g.restrictScalars ℝ).norm_iteratedFDeriv_comp_left
      (ha.contDiffAt (hU.mem_nhds (hs (hsupport hx))))) (by simp) |>.trans
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans_eq (one_mul _)).trans
      (ha_bound x (hsupport hx) r)
  have h := norm_oscillatory_integral_le_of_phase_derivative_bounds (μ := μ) hU e ψ (g ∘ a) q
    hψ hga (hsupport.trans hs) hgc hδ hL hR hgap hupper
    (fun x hx j hj ↦ hp x (hsupport hx) j hj) hgan
  have heq : (∫ x, phaseOscillation ψ x * (g ∘ a) x ∂μ) =
      g (∫ x, phaseOscillation ψ x • a x ∂μ) := by
    rw [← g.integral_comp_comm (integrable_phaseOscillation_smul hU ψ a hψ ha hs hc)]
    simp only [map_smul, smul_eq_mul, Function.comp_apply]
  rw [heq, hv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left (measureReal_mono hsupport hc.measure_lt_top.ne)
  have hB := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e δ G P) hC q 0
  positivity
end JanetCartan.Localization
