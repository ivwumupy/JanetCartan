module

public import JanetCartan.Analysis.Microlocal.Localization.Source
public import JanetCartan.Analysis.Microlocal.Localization.FourierPhase
public import JanetCartan.Analysis.Microlocal.Localization.SpectralEstimate
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Nonstationary decay of averaged vector-valued Fourier kernels

The pointwise estimate in `app:ch_osc:prop:osc-source-shell` for the actual
signed Fourier phase and a finite complex parameter measure. All derivative
constants and the common support volume remain explicit. Identification with
the Fourier transform of the source is a separate Fubini step.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory
namespace JanetCartan.Localization

variable {D E F ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_osc:prop:osc-source-shell`: Parameter-averaged vector kernels obey repeated
integration-by-parts decay away from the exact gradient, with no derivative assumptions on
reciprocal coefficients. -/
theorem norm_averagedFourierKernel_le_of_phase_gap {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (e : OrthonormalBasis ι ℝ E) (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (ξ : E →L[ℝ] ℝ) (q : ℕ)
    (hφ : ∀ u, ContDiffOn ℝ ∞ (φ u) U) (ha : ∀ u, ContDiffOn ℝ ∞ (a u) U)
    (hs : ∀ u, tsupport (a u) ⊆ K)
    {c₁ G A L ρ : ℝ} (hc₁ : 0 < c₁) (hA : 0 ≤ A) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hgap : ∀ u x, x ∈ U → c₁ * (ρ + ‖ξ‖) ≤ ‖ρ • fderiv ℝ (φ u) x - ξ‖)
    (hupper : ∀ u x, x ∈ U → ‖fderiv ℝ (φ u) x‖ ≤ G)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ u x, x ∈ tsupport (a u) → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (φ u) x‖ ≤ P j * L ^ j)
    (ha_bound : ∀ u x, x ∈ tsupport (a u) → ∀ r,
      ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * (A * L ^ r)) :
    ‖averagedFourierKernel μ ν φ a ρ ξ‖ ≤
      ((transposeDerivativeConstant e
        (phaseCoefficientDerivativeBound e (c₁ ^ 2) (max G 1) P) C q 0 *
          (A * (L / (ρ + ‖ξ‖)) ^ q)) * μ.real K) * ν.variation.real Set.univ := by
  apply norm_parameter_oscillatory_integral_le hU hK hKU e
    (fun u ↦ fourierPhase (φ u) ρ ξ) a q ν
    (fun u ↦ ((hφ u).const_smul ρ).sub ξ.contDiff.contDiffOn) ha hs
    (sq_pos_of_pos hc₁) hA hL (add_pos_of_pos_of_nonneg hρ (norm_nonneg _))
    _ _ hC _ ha_bound
  · intro u x hx
    rw [phaseGradientSquare_orthonormalBasis, fderiv_fourierPhase (φ u) ρ ξ
      (((hφ u).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hc₁.le (add_nonneg hρ.le (norm_nonneg _))) (hgap u x hx) 2
  · intro u x hx
    exact norm_fderiv_fourierPhase_le hU (φ u) ξ (hφ u) hρ.le hx (hupper u x hx)
  · intro u x hx j hj
    rw [norm_iteratedFDeriv_fourierPhase hU (φ u) ρ ξ (hφ u) (hKU (hs u hx)) hj,
      abs_of_pos hρ]
    calc
      _ ≤ ρ * (P j * L ^ j) := mul_le_mul_of_nonneg_left (hp u x hx j hj) hρ.le
      _ ≤ P j * (ρ + ‖ξ‖) * L ^ j := by
        nlinarith [mul_nonneg (mul_nonneg (hP j) (norm_nonneg ξ)) (pow_nonneg hL j)]

/-- `app:ch_osc:eq:osc-source-tail`: Decay on the full radial-mask complement for
vector-valued amplitudes and finite complex parameter measures. The constants are independent
of frequency, and include all phase and amplitude derivative profiles. -/
theorem norm_masked_averagedFourierKernel_le {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (e : OrthonormalBasis ι ℝ E) (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (π : (E →L[ℝ] ℝ) → ℂ)
    (ξ : E →L[ℝ] ℝ) (q : ℕ)
    (hφ : ∀ u, ContDiffOn ℝ ∞ (φ u) U) (ha : ∀ u, ContDiffOn ℝ ∞ (a u) U)
    (hs : ∀ u, tsupport (a u) ⊆ K)
    {c G A L ρ W : ℝ} (hc : 0 < c) (hG : 0 < G) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hW : 0 ≤ W)
    (hlower : ∀ u x, x ∈ U → c ≤ ‖fderiv ℝ (φ u) x‖)
    (hupper : ∀ u x, x ∈ U → ‖fderiv ℝ (φ u) x‖ ≤ G)
    (hπ : ∀ η, c * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * G * ρ → π η = 1)
    (hmask : ‖1 - π ξ‖ ≤ W)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ u x, x ∈ tsupport (a u) → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (φ u) x‖ ≤ P j * L ^ j)
    (ha_bound : ∀ u x, x ∈ tsupport (a u) → ∀ r,
      ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * (A * L ^ r)) :
    ‖(1 - π ξ) • averagedFourierKernel μ ν φ a ρ ξ‖ ≤
      (W * transposeDerivativeConstant e
        (phaseCoefficientDerivativeBound e ((radialGapConstant c G) ^ 2) (max G 1) P) C q 0 *
          A * μ.real K * ν.variation.real Set.univ) * (L / (ρ + ‖ξ‖)) ^ q := by
  have hB := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e ((radialGapConstant c G) ^ 2) (max G 1) P) hC q 0
  by_cases hz : 1 - π ξ = 0
  · rw [hz, zero_smul, norm_zero]
    positivity
  · rw [norm_smul]
    apply (mul_le_mul hmask
      (norm_averagedFourierKernel_le_of_phase_gap hU hK hKU e ν φ a ξ q hφ ha hs
        (radialGapConstant_pos hc hG) hA hL hρ
        (fun u x hx ↦ radial_frequency_gap_of_mask hc hG hρ.le
          (hlower u x hx) (hupper u x hx) hπ hz) hupper hP hC hp ha_bound)
      (norm_nonneg _) hW).trans_eq
    ring

/-- `app:ch_osc:eq:osc-source-tail`: The Sobolev tail for averaged vector kernels, with
weighted integrability proved from the phase and amplitude bounds. Measurability of the
frequency data is explicit; identifying these kernels with the source transform remains separate. -/
theorem sobolev_tail_averagedFourierKernel_le {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (e : OrthonormalBasis ι ℝ E) (ν : ComplexMeasure D) [IsFiniteMeasure ν.variation]
    (φ : D → E → ℝ) (a : D → E → F) (π : (E →L[ℝ] ℝ) → ℂ)
    (q : ℕ)
    (hφ : ∀ u, ContDiffOn ℝ ∞ (φ u) U) (ha : ∀ u, ContDiffOn ℝ ∞ (a u) U)
    (hs : ∀ u, tsupport (a u) ⊆ K)
    {c G A L ρ W : ℝ} (hc : 0 < c) (hG : 0 < G) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hρ : 1 ≤ ρ) (hW : 0 ≤ W)
    (hlower : ∀ u x, x ∈ U → c ≤ ‖fderiv ℝ (φ u) x‖)
    (hupper : ∀ u x, x ∈ U → ‖fderiv ℝ (φ u) x‖ ≤ G)
    (hπ : ∀ η, c * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * G * ρ → π η = 1)
    (hmask : ∀ ξ, ‖1 - π ξ‖ ≤ W)
    {P C : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hC : ∀ r, 0 ≤ C r)
    (hp : ∀ u x, x ∈ tsupport (a u) → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (φ u) x‖ ≤ P j * L ^ j)
    (ha_bound : ∀ u x, x ∈ tsupport (a u) → ∀ r,
      ‖iteratedFDeriv ℝ r (a u) x‖ ≤ C r * (A * L ^ r))
    {μξ : Measure E} [μξ.IsAddHaarMeasure] {m : ℝ} (hm : 0 ≤ m)
    (hq : m + (Module.finrank ℝ E : ℝ) / 2 < q)
    (hHm : AEStronglyMeasurable (fun ξ : E ↦
      (1 - π (InnerProductSpace.toDual ℝ E ξ)) •
        averagedFourierKernel μ ν φ a ρ (InnerProductSpace.toDual ℝ E ξ)) μξ) :
    let H := fun ξ : E ↦ (1 - π (InnerProductSpace.toDual ℝ E ξ)) •
      averagedFourierKernel μ ν φ a ρ (InnerProductSpace.toDual ℝ E ξ)
    let B := W * transposeDerivativeConstant e
      (phaseCoefficientDerivativeBound e ((radialGapConstant c G) ^ 2) (max G 1) P) C q 0 *
        A * μ.real K * ν.variation.real Set.univ
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ m * ‖H ξ‖ ^ 2) μξ ∧
      fourierWeightedL2Norm μξ m H ≤
        (B * Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * m)) ∂μξ)) *
          (ρ ^ (m + (Module.finrank ℝ E : ℝ) / 2) * (L / ρ) ^ q) := by
  dsimp only
  have hdecay (ξ : E) := norm_masked_averagedFourierKernel_le (μ := μ) hU hK hKU e ν φ a π
    (InnerProductSpace.toDual ℝ E ξ) q hφ ha hs hc hG hA hL (by positivity) hW
    hlower hupper hπ (hmask _) hP hC hp ha_bound
  simp only [LinearIsometryEquiv.norm_map] at hdecay
  have hB := transposeDerivativeConstant_nonneg e
    (phaseCoefficientDerivativeBound_nonneg e ((radialGapConstant c G) ^ 2) (max G 1) P) hC q 0
  exact ⟨integrable_sobolevEnergy_of_scaleRatio hρ hm hq hHm hdecay,
    fourierWeightedL2Norm_le_of_scaleRatio hρ hL hm hq (by positivity) hHm hdecay⟩

end JanetCartan.Localization
