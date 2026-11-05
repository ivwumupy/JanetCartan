module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.BufferedDecay

/-!
# The conjugate-transposed cross-quantization kernel

The literal adjoint retains the same symbols and physical Fourier normalization.
The two frequency weights in the checked forward estimate supply the adjoint
weight without an appeal to an L² adjoint norm. Consumer: the adjoint half of
the cross-quantization estimate in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory Set FourierTransform Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph

variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The literal adjoint Fourier kernel, with no change of quantization or
symbols (`app:ch_regular:eq:chain-tail`). -/
def crossQuantizationAdjointFourierKernel (ρ : ℝ) (mi mo : LocalizerSymbol n)
    (ξ η : E) : ℂ :=
  star (crossQuantizationFourierKernel ρ mi mo η ξ)

/-- The explicit adjoint amplitude is `mi(z,ξ/ρ) (1-mo(z,η/ρ))`.
Conjugation reverses the phase and preserves the physical `2π` factor
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjointFourierKernel_eq_integral
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (ξ η : E) :
    crossQuantizationAdjointFourierKernel ρ mi mo ξ η =
      (((2 * Real.pi) ^ n : ℝ)⁻¹ : ℂ) * ∫ z,
        Complex.exp (Complex.I * (-(inner ℝ z (ξ - η)) : ℝ)) *
          ((mi (z, ρ⁻¹ • ξ) * (1 - mo (z, ρ⁻¹ • η)) : ℝ) : ℂ) := by
  simp only [crossQuantizationAdjointFourierKernel, crossQuantizationFourierKernel,
    Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal, ← integral_conj, ← Complex.exp_conj,
    Complex.conj_I]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  · congr 1
    simp only [inner_sub_right]
    push_cast
    ring
  · rw [mul_comm]

/-- Joint smoothness of the literal adjoint kernel is inherited by conjugate
transposition (`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_crossQuantizationAdjointFourierKernel
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi)
    (his : HasCompactSupport mi) (ho : ContDiff ℝ ∞ mo) :
    ContDiff ℝ ∞ (fun p : E × E ↦
      crossQuantizationAdjointFourierKernel ρ mi mo p.1 p.2) := by
  change ContDiff ℝ ∞ (Complex.conjCLE ∘
    (fun p : E × E ↦ crossQuantizationFourierKernel ρ mi mo p.2 p.1))
  apply Complex.conjCLE.contDiff.comp
  exact (contDiff_crossQuantizationFourierKernel ρ mi mo hi his ho).comp
    (f := Prod.swap) (contDiff_snd.prodMk contDiff_fst)

/-- Exact adjoint cancellation inside the same full-support buffer
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjointFourierKernel_eq_zero_of_buffer
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (δ : ℝ)
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1)
    (ξ η : E) (hgap : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ ≤ δ) :
    crossQuantizationAdjointFourierKernel ρ mi mo ξ η = 0 := by
  simp only [crossQuantizationAdjointFourierKernel,
    crossQuantizationFourierKernel_eq_zero_of_buffer ρ mi mo δ hbuffer η ξ
      (by simpa only [norm_sub_rev] using hgap), star_zero]

/-- All joint adjoint kernel jets vanish in the strict plateau buffer.
This is exact local cancellation, before any derivative estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjointFourierKernel_jet_eq_zero_of_buffer
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (δ : ℝ)
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1)
    (ξ η : E) (hgap : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ < δ) (k : ℕ) :
    iteratedFDeriv ℝ k (fun p : E × E ↦
      crossQuantizationAdjointFourierKernel ρ mi mo p.1 p.2) (ξ, η) = 0 := by
  have he : (fun p : E × E ↦ crossQuantizationAdjointFourierKernel ρ mi mo p.1 p.2)
      =ᶠ[𝓝 (ξ, η)] fun _ ↦ (0 : ℂ) := by
    have hc : Continuous (fun p : E × E ↦ ‖ρ⁻¹ • p.1 - ρ⁻¹ • p.2‖) :=
      ((continuous_fst.const_smul ρ⁻¹).sub (continuous_snd.const_smul ρ⁻¹)).norm
    filter_upwards [(isOpen_lt hc continuous_const).eventually_mem hgap] with p hp
    exact crossQuantizationAdjointFourierKernel_eq_zero_of_buffer
      ρ mi mo δ hbuffer p.1 p.2 hp.le
  simpa using (he.iteratedFDeriv ℝ k).eq_of_nhds

/-- The adjoint output frequency lies in the original inner symbol carrier
(`app:ch_regular:eq:chain-tail`). -/
theorem crossQuantizationAdjointFourierKernel_zero_off_output
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (ξ η : E)
    (hξ : ρ⁻¹ • ξ ∉ Prod.snd '' tsupport mi) :
    crossQuantizationAdjointFourierKernel ρ mi mo ξ η = 0 := by
  simp [crossQuantizationAdjointFourierKernel,
    crossQuantizationFourierKernel_zero_off_input ρ mi mo η ξ hξ]

/-- Uniform weighted decay of the literal adjoint kernel from the SAME
primitive profiles, compact carrier, annular upper bound and positive buffer.
The fixed loss is independent of accuracy; no adjoint operator estimate is
assumed (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantizationAdjointFourierKernel_weighted_decay
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
        ((1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m) * (1 + ‖ξ - η‖) ^ M *
            ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ ≤
          C N * ρ ^ m * L ^ (m + M + (bo + bi)) * (L / ρ) ^ N := by
  obtain ⟨C, hC, h⟩ := exists_crossQuantizationFourierKernel_weighted_decay
    K hK Di Do hDi hDo bi bo hδ hR m M
  refine ⟨C, hC, ?_⟩
  intro mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η
  simpa only [crossQuantizationAdjointFourierKernel, norm_star, norm_sub_rev,
    add_comm ((1 + ‖η‖) ^ m)] using
    h mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N η ξ

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
