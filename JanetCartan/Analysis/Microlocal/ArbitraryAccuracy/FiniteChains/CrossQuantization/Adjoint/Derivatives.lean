module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Adjoint.Action
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Differentiated inverse Fourier action of the literal adjoint

Schwartz moments justify every spatial derivative under the inverse Fourier
integral. The resulting multilinear kernel multiplies the same literal
adjoint Fourier kernel by output frequency factors. Its uniform estimates
are constructed from the primitive mask profiles through the checked
two-frequency weighted decay. No differentiated-decay premise is introduced.
Consumer: the adjoint Sobolev extension in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph KernelLimits

variable {n r : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def physicalInversePairing : E →L[ℝ] E →L[ℝ] ℝ :=
  -(2 * Real.pi)⁻¹ • innerSL ℝ

private theorem physicalInversePairing_phase (ξ x : E) :
    (Real.fourierChar (-physicalInversePairing ξ x) : ℂ) =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
  rw [Real.fourierChar_apply]
  congr 1
  have h : 2 * Real.pi * (-physicalInversePairing ξ x) = inner ℝ x ξ := by
    change 2 * Real.pi * (-(-(2 * Real.pi)⁻¹ * inner ℝ ξ x)) = inner ℝ x ξ
    rw [real_inner_comm ξ x]
    field_simp
  rw [h, mul_comm]

private theorem norm_physicalInversePairing_le :
    ‖(physicalInversePairing : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ (2 * Real.pi)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖-(2 * Real.pi)⁻¹ * inner ℝ ξ x‖ ≤ (2 * Real.pi)⁻¹ * ‖ξ‖ * ‖x‖
  rw [norm_mul, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (‖ξ‖ * ‖x‖) := mul_le_mul_of_nonneg_left
      (norm_inner_le_norm ξ x) (by positivity)
    _ = _ := by ring

private theorem schwartz_derivative_physicalFourierIntegral
    (w : SchwartzMap E (Fin r → ℂ)) (m : ℕ) (x : E) (v : Fin m → E) :
    iteratedFDeriv ℝ m (w : E → Fin r → ℂ) x v =
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        (VectorFourier.fourierPowSMulRight physicalInversePairing
          (channelFourierTransform w) ξ m v) := by
  have he : (w : E → Fin r → ℂ) = VectorFourier.fourierIntegral
      Real.fourierChar volume physicalInversePairing.toLinearMap₁₂
        (channelFourierTransform w) := by
    funext y
    change w y = ∫ ξ, (Real.fourierChar (-physicalInversePairing ξ y) : ℂ) •
      channelFourierTransform w ξ
    simp_rw [physicalInversePairing_phase]
    exact (channelFourierTransform_inversion w y).symm
  rw [he, VectorFourier.iteratedFDeriv_fourierIntegral physicalInversePairing
    (N := ⊤) (fun j _ ↦ (channelFourierTransform w).integrable_pow_mul volume j)
    (channelFourierTransform w).continuous.aestronglyMeasurable (by simp)]
  rw [VectorFourier.fourierIntegral_continuousMultilinearMap_apply
    Real.continuous_fourierChar (VectorFourier.integrable_fourierPowSMulRight
      physicalInversePairing ((channelFourierTransform w).integrable_pow_mul volume m)
        (channelFourierTransform w).continuous.aestronglyMeasurable)]
  change (∫ ξ, (Real.fourierChar (-physicalInversePairing ξ x) : ℂ) •
    VectorFourier.fourierPowSMulRight physicalInversePairing
      (channelFourierTransform w) ξ m v) = _
  simp_rw [physicalInversePairing_phase]

/-- The multilinear multiplier kernel for `m` physical output derivatives
of the literal adjoint inverse Fourier integral. The bilinear pairing uses
`-(2π)⁻¹ inner`, exactly cancelling the Fourier convention's derivative
factor `-2πI` (`app:ch_regular:eq:chain-tail`). -/
def crossQuantizationAdjointDerivativeKernel (ρ : ℝ) (mi mo : LocalizerSymbol n)
    (m : ℕ) (ξ η : E) : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) ℂ :=
  VectorFourier.fourierPowSMulRight (-(2 * Real.pi)⁻¹ • innerSL ℝ)
    (fun ζ ↦ crossQuantizationAdjointFourierKernel ρ mi mo ζ η) ξ m

/-- The explicit physical derivative multiplier has no leftover `2π`
factor: each output derivative contributes `I * inner ξ v`
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjointDerivativeKernel_apply
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (m : ℕ) (ξ η : E) (v : Fin m → E) :
    crossQuantizationAdjointDerivativeKernel ρ mi mo m ξ η v =
      Complex.I ^ m * (∏ j, (inner ℝ ξ (v j) : ℂ)) *
        crossQuantizationAdjointFourierKernel ρ mi mo ξ η := by
  rw [crossQuantizationAdjointDerivativeKernel, VectorFourier.fourierPowSMulRight_apply]
  change (-(2 * ↑Real.pi * Complex.I)) ^ m •
    (∏ j, -(2 * Real.pi)⁻¹ * inner ℝ ξ (v j)) •
      crossQuantizationAdjointFourierKernel ρ mi mo ξ η = _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.ofReal_prod]
  rw [← mul_assoc, ← mul_assoc, ← mul_pow]
  have hc : -(2 * ↑Real.pi * Complex.I) * -(2 * (Real.pi : ℂ))⁻¹ = Complex.I := by
    field_simp
  rw [hc]

/-- Exact differentiated inverse Fourier test action. The Fourier-action
premise is produced for the SAME bounded adjoint by
`bounded_crossQuantization_adjoint_schwartz_fourier_action`. Schwartz moments
justify differentiation at every order; no datum derivative enters the
kernel (`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjoint_iteratedFDeriv_test_action
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (f w : SchwartzMap E (Fin r → ℂ))
    (hw : ∀ ξ, channelFourierTransform w ξ =
      ∫ η, crossQuantizationAdjointFourierKernel ρ mi mo ξ η • channelFourierTransform f η)
    (m : ℕ) (x : E) (v : Fin m → E) :
    iteratedFDeriv ℝ m (w : E → Fin r → ℂ) x v =
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        ∫ η, (crossQuantizationAdjointDerivativeKernel ρ mi mo m ξ η v) •
          channelFourierTransform f η := by
  rw [schwartz_derivative_physicalFourierIntegral]
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  rw [VectorFourier.fourierPowSMulRight_apply, hw, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [crossQuantizationAdjointDerivativeKernel, VectorFourier.fourierPowSMulRight_apply,
    physicalInversePairing, smul_assoc]

/-- The SAME bounded adjoint admits the proved Fourier action and all its
spatially differentiated inverse Fourier actions. This instantiates the
Fourier-action premise of `crossQuantizationAdjoint_iteratedFDeriv_test_action`
with its actual producer; no extra analytic hypothesis remains
(`app:ch_regular:eq:chain-tail`). -/
theorem bounded_crossQuantization_adjoint_schwartz_differentiated_action
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (ho : ContDiff ℝ ∞ mo) (hos : HasCompactSupport mo)
    (Li Ro : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E))
    (hLi : ∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hRo : ∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (f : SchwartzMap E (Fin r → ℂ)) :
    ∃ w : SchwartzMap E (Fin r → ℂ),
      ((1 - Ro).comp Li).adjoint
          ((LowBounds.FrequencyCutoff.toEuclideanSchwartz f).toLp 2)
        =ᵐ[volume] (fun x ↦ WithLp.toLp 2 (w x)) ∧
      (∀ ξ, channelFourierTransform w ξ =
        ∫ η, crossQuantizationAdjointFourierKernel ρ mi mo ξ η •
          channelFourierTransform f η) ∧
      ∀ (m : ℕ) (x : E) (v : Fin m → E),
        iteratedFDeriv ℝ m (w : E → Fin r → ℂ) x v =
          ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
            ∫ η, (crossQuantizationAdjointDerivativeKernel ρ mi mo m ξ η v) •
              channelFourierTransform f η := by
  obtain ⟨w, hw, hwF⟩ := bounded_crossQuantization_adjoint_schwartz_fourier_action
    hρ mi mo hi his ho hos Li Ro hLi hRo f
  exact ⟨w, hw, hwF, crossQuantizationAdjoint_iteratedFDeriv_test_action ρ mi mo f w hwF⟩

/-- The actual derivative multiplier has the sharp physical frequency
factor. In particular no spurious `2π` loss is introduced by switching
Fourier conventions (`app:ch_regular:eq:chain-tail`). -/
theorem norm_crossQuantizationAdjointDerivativeKernel_le
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (m : ℕ) (ξ η : E) :
    ‖crossQuantizationAdjointDerivativeKernel ρ mi mo m ξ η‖ ≤
      ‖ξ‖ ^ m * ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ := by
  have hc : 2 * Real.pi * ‖(physicalInversePairing : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 1 := by
    calc
      _ ≤ 2 * Real.pi * (2 * Real.pi)⁻¹ :=
        mul_le_mul_of_nonneg_left norm_physicalInversePairing_le (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc
    _ ≤ (2 * Real.pi * ‖(physicalInversePairing : E →L[ℝ] E →L[ℝ] ℝ)‖) ^ m *
        ‖ξ‖ ^ m * ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ :=
      VectorFourier.norm_fourierPowSMulRight_le physicalInversePairing
        (fun ζ : E ↦ crossQuantizationAdjointFourierKernel ρ mi mo ζ η) ξ m
    _ ≤ 1 ^ m * ‖ξ‖ ^ m * ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ := by
      gcongr
    _ = _ := by rw [one_pow, one_mul]

/-- Uniform decay for the differentiated inverse Fourier adjoint kernel,
constructed from the same primitive profiles and geometric data as the
undifferentiated kernel. Constants precede symbols and scales, and the
loss `m+M+bo+bi` is independent of accuracy
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantizationAdjointDerivativeKernel_weighted_decay
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (m M : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      (∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ N (ξ η : E),
        (1 + ‖ξ - η‖) ^ M * ‖crossQuantizationAdjointDerivativeKernel ρ mi mo m ξ η‖ ≤
          C N * ρ ^ m * L ^ (m + M + (bo + bi)) * (L / ρ) ^ N := by
  obtain ⟨C, hC, h⟩ := exists_crossQuantizationAdjointFourierKernel_weighted_decay
    K hK Di Do hDi hDo bi bo hδ hR m M
  refine ⟨C, hC, ?_⟩
  intro mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η
  have hw : ‖ξ‖ ^ m ≤ (1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m := by
    exact (pow_le_pow_left₀ (norm_nonneg ξ) (by linarith : ‖ξ‖ ≤ 1 + ‖ξ‖) m).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ (1 + ‖ξ - η‖) ^ M *
        (‖ξ‖ ^ m * ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖) :=
      mul_le_mul_of_nonneg_left
        (norm_crossQuantizationAdjointDerivativeKernel_le ρ mi mo m ξ η) (by positivity)
    _ ≤ (1 + ‖ξ - η‖) ^ M *
        (((1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m) *
          ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖) := by gcongr
    _ = ((1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m) * (1 + ‖ξ - η‖) ^ M *
        ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ := by ring
    _ ≤ _ := h mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
