module
public import JanetCartan.Analysis.Microlocal.Localization.Coefficients
public import JanetCartan.Analysis.Microlocal.Localization.Gap
import Mathlib.Analysis.InnerProductSpace.Dual
/-!
# Nonstationary bounds for the full Fourier phase

The pointwise kernel estimate in `app:ch_osc:prop:osc-source-shell`, derived
from the original phase bounds, with all high derivative constants retained.
The covector is exactly `ρ dφ - ξ`. The radial-mask estimate includes the
transition regions where the complementary mask is nonzero. Integrals here are
unnormalized scalar kernels; the source's Fourier normalization and parameter
integration are separate steps.
-/

open scoped ContDiff
open Set
@[expose] public noncomputable section
namespace JanetCartan.Localization
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  [FiniteDimensional ℝ E]
/-- `app:ch_osc:prop:osc-source-shell`: In an orthonormal basis, the sum of squared covector components equals its squared operator norm. -/
theorem covectorSquare_orthonormalBasis (e : OrthonormalBasis ι ℝ E) (v : E →L[ℝ] ℝ) :
    covectorSquare e v = ‖v‖ ^ 2 := by
  have h := e.sum_sq_norm_inner_left ((InnerProductSpace.toDual ℝ E).symm v)
  simpa only [covectorSquare, InnerProductSpace.toDual_symm_apply, Real.norm_eq_abs, sq_abs,
    LinearIsometryEquiv.norm_map] using h
/-- `app:ch_osc:prop:osc-source-shell`: The denominator of the phase operator is the squared norm of the actual phase gradient. -/
theorem phaseGradientSquare_orthonormalBasis (e : OrthonormalBasis ι ℝ E) (ψ : E → ℝ) (x : E) :
    phaseGradientSquare e ψ x = ‖fderiv ℝ ψ x‖ ^ 2 :=
  covectorSquare_orthonormalBasis e _
omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: Every derivative of order at least two of the full Fourier phase has the exact factor `|ρ|`; the frequency term is linear. -/
theorem norm_iteratedFDeriv_fourierPhase {U : Set E} (hU : IsOpen U)
    (φ : E → ℝ) (ρ : ℝ) (ξ : E →L[ℝ] ℝ) (hφ : ContDiffOn ℝ ∞ φ U)
    {x : E} (hx : x ∈ U) {j : ℕ} (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ (j + 1) (fourierPhase φ ρ ξ) x‖ =
      |ρ| * ‖iteratedFDeriv ℝ (j + 1) φ x‖ := by
  have hlin : iteratedFDeriv ℝ (j + 1) ξ x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv]
    have heq : fderiv ℝ ξ = fun _ ↦ ξ := funext (fun _ ↦ ξ.fderiv)
    rw [heq, iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, norm_zero]
  have hc : ContDiffAt ℝ (j + 1) φ x :=
    (hφ.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  change ‖iteratedFDeriv ℝ (j + 1) ((fun y ↦ ρ • φ y) - (ξ : E → ℝ)) x‖ = _
  rw [iteratedFDeriv_sub_apply (i := j + 1) (hc.const_smul ρ) ξ.contDiff.contDiffAt, hlin, sub_zero,
    iteratedFDeriv_const_smul_apply' (i := j + 1) (a := ρ) hc, norm_smul, Real.norm_eq_abs]

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- `app:ch_osc:prop:osc-source-shell`: The full Fourier gradient is bounded by `max G 1` times the radial frequency scale. -/
theorem norm_fderiv_fourierPhase_le {U : Set E} (hU : IsOpen U)
    (φ : E → ℝ) {ρ C : ℝ} (ξ : E →L[ℝ] ℝ) (hφ : ContDiffOn ℝ ∞ φ U)
    (hρ : 0 ≤ ρ) {x : E} (hx : x ∈ U) (hupper : ‖fderiv ℝ φ x‖ ≤ C) :
    ‖fderiv ℝ (fourierPhase φ ρ ξ) x‖ ≤ max C 1 * (ρ + ‖ξ‖) := by
  rw [fderiv_fourierPhase φ ρ ξ ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
  have h1 := mul_le_mul_of_nonneg_left (hupper.trans (le_max_left C 1)) hρ
  have h2 := mul_le_mul_of_nonneg_right (le_max_right C 1) (norm_nonneg ξ)
  nlinarith

open MeasureTheory
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
/-- `app:ch_osc:prop:osc-source-shell`: Repeated integration by parts away from the actual signed gradient difference, with no coefficient derivative hypothesis. -/
theorem norm_fourier_integral_le_of_phase_gap {U : Set E} (hU : IsOpen U)
    (e : OrthonormalBasis ι ℝ E) (φ : E → ℝ) (a : E → ℂ) (ξ : E →L[ℝ] ℝ) (q : ℕ)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    {c₁ G A L ρ : ℝ} (hc₁ : 0 < c₁) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hgap : ∀ x ∈ U, c₁ * (ρ + ‖ξ‖) ≤ ‖ρ • fderiv ℝ φ x - ξ‖)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j)
    (hp : ∀ x ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * L ^ j)
    (ha_bound : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖∫ x, phaseOscillation (fourierPhase φ ρ ξ) x * a x ∂μ‖ ≤
      (transposeDerivativeConstant e (phaseCoefficientDerivativeBound e (c₁ ^ 2) (max G 1) P) C q 0 *
        (A * (L / (ρ + ‖ξ‖)) ^ q)) * μ.real (tsupport a) := by
  have hψ : ContDiffOn ℝ ∞ (fourierPhase φ ρ ξ) U :=
    (hφ.const_smul ρ).sub ξ.contDiff.contDiffOn
  apply norm_oscillatory_integral_le_of_phase_derivative_bounds hU e (fourierPhase φ ρ ξ) a q
    hψ ha hs hc (sq_pos_of_pos hc₁) hL (add_pos_of_pos_of_nonneg hρ (norm_nonneg _))
    _ _ _ ha_bound
  · intro x hx
    rw [phaseGradientSquare_orthonormalBasis,
      fderiv_fourierPhase φ ρ ξ ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hc₁.le (add_nonneg hρ.le (norm_nonneg _))) (hgap x hx) 2
  · intro x hx
    exact norm_fderiv_fourierPhase_le hU φ ξ hφ hρ.le hx (hupper x hx)
  · intro x hx j hj
    rw [norm_iteratedFDeriv_fourierPhase hU φ ρ ξ hφ (hs hx) hj, abs_of_pos hρ]
    calc
      _ ≤ ρ * (P j * L ^ j) := mul_le_mul_of_nonneg_left (hp x hx j hj) hρ.le
      _ ≤ P j * (ρ + ‖ξ‖) * L ^ j := by
        nlinarith [mul_nonneg (hP j) (norm_nonneg ξ), pow_nonneg hL j,
          mul_nonneg (mul_nonneg (hP j) (norm_nonneg ξ)) (pow_nonneg hL j)]

/-- `app:ch_osc:prop:osc-source-shell`: The pointwise tail bound for a radial mask, including all transition regions. The displayed constants are independent of `ρ` and `ξ`. -/
theorem norm_masked_fourier_integral_le {U : Set E} (hU : IsOpen U)
    (e : OrthonormalBasis ι ℝ E) (φ : E → ℝ) (a : E → ℂ)
    (π : (E →L[ℝ] ℝ) → ℂ) (ξ : E →L[ℝ] ℝ) (q : ℕ)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (hc : HasCompactSupport a)
    {c G A L ρ W : ℝ} (hcpos : 0 < c) (hG : 0 < G)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hρ : 0 < ρ) (hW : 0 ≤ W)
    (hlower : ∀ x ∈ U, c ≤ ‖fderiv ℝ φ x‖)
    (hupper : ∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G)
    (hπ : ∀ η, c * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * G * ρ → π η = 1)
    (hmask : ‖1 - π ξ‖ ≤ W)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ x ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ x‖ ≤ P j * L ^ j)
    (ha_bound : ∀ x ∈ tsupport a, ∀ r,
      ‖iteratedFDeriv ℝ r a x‖ ≤ C r * (A * L ^ r)) :
    ‖(1 - π ξ) * ∫ x, phaseOscillation (fourierPhase φ ρ ξ) x * a x ∂μ‖ ≤
      W * ((transposeDerivativeConstant e
        (phaseCoefficientDerivativeBound e ((radialGapConstant c G) ^ 2) (max G 1) P) C q 0 *
          (A * (L / (ρ + ‖ξ‖)) ^ q)) * μ.real (tsupport a)) := by
  by_cases hz : 1 - π ξ = 0
  · rw [hz, zero_mul, norm_zero]
    have hB := transposeDerivativeConstant_nonneg e
      (phaseCoefficientDerivativeBound_nonneg e ((radialGapConstant c G) ^ 2) (max G 1) P) hC q 0
    positivity
  · rw [norm_mul]
    apply mul_le_mul hmask _ (norm_nonneg _) hW
    apply norm_fourier_integral_le_of_phase_gap hU e φ a ξ q hφ ha hs hc
      (radialGapConstant_pos hcpos hG) hL hρ _ hupper hP hp ha_bound
    intro x hx
    exact radial_frequency_gap_of_mask hcpos hG hρ.le (hlower x hx) (hupper x hx) hπ hz
end JanetCartan.Localization
