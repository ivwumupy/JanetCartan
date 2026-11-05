module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Profiles

/-!
# The uniform plateau gain for the cross Fourier kernel

A fixed buffer converts the decay proved from primitive mask profiles into
an arbitrary power of `L/ρ`. The remaining power of `L` is fixed by the
chosen spatial weight and the two primitive offsets, independently of
accuracy. Consumer: Schur bounds for the Fourier representation of the
actual cross product (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph

variable {n : ℕ}
local notation "E" => Euclidean n
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- Uniform rapid decay of the literal Fourier kernel from the primitive
mask profiles and the full-support plateau buffer. The constants precede
the symbols and scales, and the loss `M+bo+bi` is independent of accuracy.
This is a kernel estimate, not yet the all-L² Sobolev operator theorem
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantizationFourierKernel_buffered_decay
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → ContDiff ℝ ∞ mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ N (ξ η : E),
        (1 + ‖ξ - η‖) ^ M * ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ ≤
          C N * L ^ (M + (bo + bi)) * (L / ρ) ^ N := by
  obtain ⟨B, hB, hb⟩ := exists_crossQuantizationFourierKernel_frequency_decay
    K hK Di Do hDi hDo bi bo
  let a := δ / (2 * Real.pi)
  let c := min 1 (1 / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  let D N := a ^ N * c ^ M
  have hD N : 0 < D N := mul_pos (pow_pos ha _) (pow_pos hc _)
  refine ⟨fun N ↦ B (N + M) / D N, fun N ↦ div_nonneg (hB _) (hD N).le, ?_⟩
  intro mi mo hi ho hcarrier hbuffer ρ L hL hLρ hij hoj N ξ η
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  by_cases hgap : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ ≤ δ
  · rw [crossQuantizationFourierKernel_eq_zero_of_buffer ρ mi mo δ hbuffer ξ η hgap,
      norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg (hB _) (hD N).le)
      (pow_nonneg (zero_le_one.trans hL) _))
        (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ.le) _)
  have hd : δ * ρ ≤ ‖ξ - η‖ := by
    have hnorm : ‖ρ⁻¹ • ξ - ρ⁻¹ • η‖ = ‖ξ - η‖ / ρ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
      ring
    rw [hnorm] at hgap
    exact (le_div_iff₀ hρ).mp (le_of_lt (lt_of_not_ge hgap))
  let w := 1 + ‖(2 * Real.pi)⁻¹ • (ξ - η)‖
  have hw : w = 1 + (2 * Real.pi)⁻¹ * ‖ξ - η‖ := by
    simp only [w, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  have hfreq : ρ * a ≤ w := by
    rw [hw]
    calc
      _ = (2 * Real.pi)⁻¹ * (δ * ρ) := by dsimp [a]; ring
      _ ≤ (2 * Real.pi)⁻¹ * ‖ξ - η‖ := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := by linarith
  have hspace : c * (1 + ‖ξ - η‖) ≤ w := by
    rw [hw]
    have hc' : c ≤ (2 * Real.pi)⁻¹ := by
      simpa only [c, one_div] using (min_le_right (1 : ℝ) (1 / (2 * Real.pi)))
    calc
      _ = c + c * ‖ξ - η‖ := by ring
      _ ≤ _ := add_le_add (min_le_left _ _)
        (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))
  have hcombined : (ρ ^ N * D N) *
      ((1 + ‖ξ - η‖) ^ M * ‖crossQuantizationFourierKernel ρ mi mo ξ η‖) ≤
        B (N + M) * L ^ (N + M + (bo + bi)) := by
    calc
      _ = ((ρ * a) ^ N * (c * (1 + ‖ξ - η‖)) ^ M) *
          ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ := by
            dsimp [D]
            simp only [mul_pow]
            ring
      _ ≤ (w ^ N * w ^ M) * ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ := by
        gcongr
      _ ≤ _ := by
        rw [← pow_add]
        exact hb mi mo hi ho hcarrier ρ L hL hij hoj (N + M) ξ η
  have hdiv := (le_div_iff₀ (mul_pos (pow_pos hρ N) (hD N))).mpr
    (show ((1 + ‖ξ - η‖) ^ M * ‖crossQuantizationFourierKernel ρ mi mo ξ η‖) *
      (ρ ^ N * D N) ≤ B (N + M) * L ^ (N + M + (bo + bi)) by
        simpa only [mul_comm] using hcombined)
  refine hdiv.trans_eq ?_
  rw [show N + M + (bo + bi) = (M + (bo + bi)) + N by omega, pow_add, div_pow]
  field_simp

/-- Both frequency weights of the same kernel have a uniform rapid bound.
The upper annular bound is used only on the original input symbol; the
opposite weight follows from frequency-difference decay. Thus the estimate
retains the frequency weights needed for both forward and transposed
Schur estimates. It does not infer a Sobolev adjoint bound from an L² norm
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantizationFourierKernel_weighted_decay
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
            ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ ≤
          C N * ρ ^ m * L ^ (m + M + (bo + bi)) * (L / ρ) ^ N := by
  obtain ⟨B, hB, hb⟩ := exists_crossQuantizationFourierKernel_buffered_decay
    K hK Di Do hDi hDo bi bo hδ (m + M)
  refine ⟨fun N ↦ 2 * (1 + R) ^ m * B N,
    fun N ↦ mul_nonneg (by positivity) (hB N), ?_⟩
  intro mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η
  have hρ1 : 1 ≤ ρ := hL.trans hLρ
  have hρ : 0 < ρ := zero_lt_one.trans_le hρ1
  by_cases hz : crossQuantizationFourierKernel ρ mi mo ξ η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hB N))
      (pow_nonneg hρ.le _)) (pow_nonneg (zero_le_one.trans hL) _))
        (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ.le) _)
  have hη : ρ⁻¹ • η ∈ Prod.snd '' tsupport mi := by
    by_contra hnot
    exact hz (crossQuantizationFourierKernel_zero_off_input ρ mi mo ξ η hnot)
  obtain ⟨p, hp, he⟩ := hη
  have hηnorm : ‖η‖ ≤ ρ * R := by
    have hsmall : ‖ρ⁻¹ • η‖ ≤ R := he ▸ hann p hp
    have hid : η = ρ • (ρ⁻¹ • η) := by simp [smul_smul, hρ.ne']
    calc
      ‖η‖ = ρ * ‖ρ⁻¹ • η‖ := by conv_lhs => rw [hid]; rw [norm_smul, Real.norm_of_nonneg hρ.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hρ.le
  have heta : 1 + ‖η‖ ≤ (1 + R) * ρ := by nlinarith
  have hxi : 1 + ‖ξ‖ ≤ ((1 + R) * ρ) * (1 + ‖ξ - η‖) := by
    have hn : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ξ - η) η
    calc
      _ ≤ 1 + ‖ξ - η‖ + ‖η‖ := by linarith
      _ ≤ (1 + ‖η‖) * (1 + ‖ξ - η‖) := by
        nlinarith [mul_nonneg (norm_nonneg η) (norm_nonneg (ξ - η))]
      _ ≤ _ := mul_le_mul_of_nonneg_right heta (by positivity)
  have heta' : 1 + ‖η‖ ≤ ((1 + R) * ρ) * (1 + ‖ξ - η‖) := by
    exact heta.trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (norm_nonneg _)))
  have hweights : (1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m ≤
      2 * (((1 + R) * ρ) * (1 + ‖ξ - η‖)) ^ m := by
    have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖ξ‖) hxi m
    have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖η‖) heta' m
    linarith
  calc
    _ ≤ (2 * (((1 + R) * ρ) * (1 + ‖ξ - η‖)) ^ m) * (1 + ‖ξ - η‖) ^ M *
        ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ := by gcongr
    _ = (2 * (1 + R) ^ m * ρ ^ m) *
        ((1 + ‖ξ - η‖) ^ (m + M) * ‖crossQuantizationFourierKernel ρ mi mo ξ η‖) := by
      simp only [mul_pow, pow_add]
      ring
    _ ≤ (2 * (1 + R) ^ m * ρ ^ m) *
        (B N * L ^ (m + M + (bo + bi)) * (L / ρ) ^ N) :=
      mul_le_mul_of_nonneg_left
        (hb mi mo hi ho hcarrier hbuffer ρ L hL hLρ hij hoj N ξ η) (by positivity)
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
