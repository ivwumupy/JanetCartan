module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fourier

/-!
# Physical Fourier normalization for the cross-kernel endpoint

The reusable endpoint for `app:ch_regular:eq:chain-tail` consumes the literal
`channelFourierTransform` action. Rescaling both covectors to Mathlib's Fourier
convention contributes exactly `(2π)^n` to the kernel. The polynomial kernel
bound survives this rescaling with a dimension-only factor.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph.KernelLimits

variable {n r : ℕ}
local notation "E" => Euclidean n

/-- The physical Fourier kernel expressed in Mathlib's covectors. This is
the kernel consumed by the Schur endpoint for `app:ch_regular:eq:chain-tail`. -/
def normalizedCrossFourierKernel (k : E → E → ℂ) (ξ η : E) : ℂ :=
  ((2 * Real.pi) ^ n : ℝ) • k ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)

/-- Exact normalization of a literal physical Fourier action, with no
integrability or Sobolev conclusion assumed (`app:ch_regular:eq:chain-tail`). -/
theorem fourier_action_of_channelFourier_action (k : E → E → ℂ)
    (f w : SchwartzMap E (Fin r → ℂ))
    (h : ∀ ξ, channelFourierTransform w ξ =
      ∫ η, k ξ η • channelFourierTransform f η) (ξ : E) :
    (𝓕 w) ξ = ∫ η, normalizedCrossFourierKernel k ξ η • (𝓕 f) η := by
  have hc (g : SchwartzMap E (Fin r → ℂ)) (ζ : E) :
      channelFourierTransform g ((2 * Real.pi) • ζ) =
        ((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 g) ζ := by
    change ((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 g)
      ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • ζ)) = _
    simp only [smul_smul, inv_mul_cancel₀ (show 2 * Real.pi ≠ 0 by positivity), one_smul]
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun η ↦ k ((2 * Real.pi) • ξ) η • channelFourierTransform f η)
    (2 * Real.pi) (hR := by positivity)
  simp only [Euclidean, finrank_euclideanSpace_fin] at hs
  rw [← h, hc] at hs
  simp_rw [hc] at hs
  have hi (η : E) : k ((2 * Real.pi) • ξ) ((2 * Real.pi) • η) •
      (((2 * Real.pi) ^ n : ℝ)⁻¹ • (𝓕 f) η) =
      ((2 * Real.pi) ^ n : ℝ)⁻¹ •
        (k ((2 * Real.pi) • ξ) ((2 * Real.pi) • η) • (𝓕 f) η) :=
    smul_comm _ _ _
  simp_rw [hi] at hs
  rw [integral_smul] at hs
  have hh := (smul_right_injective (M := Fin r → ℂ)
    (show ((2 * Real.pi) ^ n : ℝ)⁻¹ ≠ 0 by positivity)) hs
  simp only [normalizedCrossFourierKernel, smul_assoc]
  rw [integral_smul, hh, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- Joint measurability survives the physical Fourier rescaling used by
the Schur endpoint (`app:ch_regular:eq:chain-tail`). -/
theorem stronglyMeasurable_normalizedCrossFourierKernel (k : E → E → ℂ)
    (hk : StronglyMeasurable (Function.uncurry k)) :
    StronglyMeasurable (Function.uncurry (normalizedCrossFourierKernel k)) := by
  exact (hk.comp_measurable
    ((measurable_fst.const_smul (2 * Real.pi)).prodMk
      (measurable_snd.const_smul (2 * Real.pi)))).const_smul ((2 * Real.pi) ^ n : ℝ)

/-- Rescaling the literal physical kernel preserves the required Schur
weight, with its exact dimension factor (`app:ch_regular:eq:chain-tail`). -/
theorem normalizedCrossFourierKernel_weighted_bound (m : ℕ) (k : E → E → ℂ)
    {B : ℝ}
    (hb : ∀ ξ η, (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ ≤ B)
    (ξ η : E) :
    (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) *
      ‖normalizedCrossFourierKernel k ξ η‖ ≤ (2 * Real.pi) ^ n * B := by
  have ha : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hn (x : E) : ‖x‖ ≤ ‖(2 * Real.pi) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact le_mul_of_one_le_left (norm_nonneg _) ha
  rw [normalizedCrossFourierKernel, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ n)]
  calc
    _ = (2 * Real.pi) ^ n * ((1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) *
        ‖k ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)‖) := by ring
    _ ≤ (2 * Real.pi) ^ n *
        ((1 + ‖(2 * Real.pi) • ξ‖) ^ m *
          (1 + ‖(2 * Real.pi) • ξ - (2 * Real.pi) • η‖) ^ (n + 1) *
            ‖k ((2 * Real.pi) • ξ) ((2 * Real.pi) • η)‖) := by
      rw [← smul_sub]
      gcongr
      · exact hn ξ
      · exact hn (ξ - η)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb _ _) (by positivity)

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
