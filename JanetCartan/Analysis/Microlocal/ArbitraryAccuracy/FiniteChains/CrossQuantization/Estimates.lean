module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Sobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Adjoint

/-!
# Both orientations of the cross-quantization estimate

The actual product `(1 - Ro).comp Li` and its literal Hilbert adjoint have
all-L² vector Fourier-Sobolev bounds from the primitive buffered mask data.
The fixed loss is `m + (n + 1) + (bo + bi)`, independent of accuracy, and
the power of `ρ` is exactly `m`. Constants are uniform over the symbols and
scales. The bounded realizations are chosen once for every order and accuracy.

This supplies the cross-quantization bridge between `CompleteFactor` and
`finiteChain_observation_rapidDecayAt` in `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail`. The protected-mask constructor supplies
the primitive data; its application to the same initialized family and the
composition of the actual residual chain remain with the response construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- All-L² Sobolev membership and decay for the literal cross-product
adjoint. The proof applies the Fourier-kernel endpoint to the actual adjoint
test action and the conjugate-transposed kernel bound. Its spatial derivatives
are justified by `bounded_crossQuantization_adjoint_schwartz_differentiated_action`
and `exists_crossQuantizationAdjointDerivativeKernel_weighted_decay`; no
Sobolev estimate is inferred from an L² adjoint norm. Consumer: the reverse
cross-quantization bridge in `app:ch_regular:eq:chain-tail`. -/
theorem exists_crossQuantization_adjoint_sobolev_bound
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (m : ℕ) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      (∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      ∀ N (u : H), MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li).adjoint u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li).adjoint u) ≤
          C N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨S, hS, hs⟩ := exists_channelFourierKernel_sobolev_constant (n := n) (r := r) m
  obtain ⟨C, hC, hc⟩ := exists_crossQuantizationAdjointFourierKernel_weighted_decay
    K hK Di Do hDi hDo bi bo hδ hR m (n + 1)
  refine ⟨fun N ↦ S * C N, fun N ↦ mul_nonneg hS (hC N), ?_⟩
  intro mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Ro hLi hRo N u
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let B := C N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N
  have hB : 0 ≤ B := by
    have hCN := hC N
    dsimp [B]
    positivity
  have hk : StronglyMeasurable
      (Function.uncurry (crossQuantizationAdjointFourierKernel ρ mi mo)) :=
    (contDiff_crossQuantizationAdjointFourierKernel ρ mi mo hi his ho).continuous.stronglyMeasurable
  have hb (ξ η : E) : (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) *
      ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ ≤ B := by
    calc
      _ ≤ ((1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m) * (1 + ‖ξ - η‖) ^ (n + 1) *
          ‖crossQuantizationAdjointFourierKernel ρ mi mo ξ η‖ := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
      _ ≤ B := hc mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η
  have h := hs (crossQuantizationAdjointFourierKernel ρ mi mo) hk B hB hb
    ((1 - Ro).comp Li).adjoint
    (bounded_crossQuantization_adjoint_schwartz_fourier_action
      hρ.ne' mi mo hi his ho hos Li Ro hLi hRo) u
  refine ⟨h.1, ?_⟩
  simpa only [B, mul_assoc] using h.2

/-- Uniform bounds for both orientations of the SAME cross-quantization
operator, simultaneously at every Sobolev order and accuracy. Constants
precede the symbols, scales and bounded realizations, so this applies to a
family with common primitive profiles, compact carrier and plateau buffer.
The loss `m + (n + 1) + (bo + bi)` is independent of `N`, and `C_A = 0`.
Consumer: connecting the actual complete residual factors to
`finiteChain_observation_rapidDecayAt` (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantization_twoSided_sobolev_bounds
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ∃ C : ℕ → ℕ → ℝ, (∀ m N, 0 ≤ C m N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      (∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      ∀ (m N : ℕ) (u : H),
        (MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li) u) ∧
          vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li) u) ≤
            C m N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖) ∧
        (MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li).adjoint u) ∧
          vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li).adjoint u) ≤
            C m N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖) := by
  choose Cf hCf hf using fun m ↦ exists_crossQuantization_sobolev_bound
    (r := r) K hK Di Do hDi hDo bi bo hδ hR m
  choose Ca hCa ha using fun m ↦ exists_crossQuantization_adjoint_sobolev_bound
    (r := r) K hK Di Do hDi hDo bi bo hδ hR m
  refine ⟨fun m N ↦ Cf m N + Ca m N, fun m N ↦ add_nonneg (hCf m N) (hCa m N), ?_⟩
  intro mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Ro hLi hRo m N u
  have hρ : 0 ≤ ρ := zero_le_one.trans (hL.trans hLρ)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  obtain ⟨hfmem, hfbound⟩ :=
    hf m mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Ro hLi hRo N u
  obtain ⟨hamem, habound⟩ :=
    ha m mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Ro hLi hRo N u
  refine ⟨⟨hfmem, hfbound.trans ?_⟩, ⟨hamem, habound.trans ?_⟩⟩
  · gcongr
    exact le_add_of_nonneg_right (hCa m N)
  · gcongr
    exact le_add_of_nonneg_left (hCf m N)

/-- Construct the bounded physical localizers once and obtain both Sobolev
estimates for every order and accuracy. This closes the realization premises
of `exists_crossQuantization_twoSided_sobolev_bounds` using the existing
physical-localizer constructor. The only inputs are smooth real compact mask
data, the full-support buffer, and primitive derivative profiles; no kernel
decay or successful operator estimate is assumed. The consuming response
construction must instantiate these data on its SAME initialized family
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_bounded_crossQuantization_twoSided_sobolev_bounds
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ∃ C : ℕ → ℕ → ℝ, (∀ m N, 0 ≤ C m N) ∧
      ∀ (mi mo : LocalizerSymbol n), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      (∀ p ∈ tsupport mi, ∀ q : E × E, dist q p ≤ δ → mo q = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∃ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ∀ (m N : ℕ) (u : H),
        (MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li) u) ∧
          vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li) u) ≤
            C m N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖) ∧
        (MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li).adjoint u) ∧
          vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li).adjoint u) ≤
            C m N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖) := by
  obtain ⟨C, hC, hc⟩ := exists_crossQuantization_twoSided_sobolev_bounds
    (r := r) K hK Di Do hDi hDo bi bo hδ hR
  refine ⟨C, hC, ?_⟩
  intro mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj
  have hρ : ρ ≠ 0 := (zero_lt_one.trans_le (hL.trans hLρ)).ne'
  obtain ⟨Li, hLi, _⟩ := EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers
    (q := r) hρ mi hi.continuous his
  obtain ⟨Lo, _, hRo⟩ := EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers
    (q := r) hρ mo ho.continuous hos
  exact ⟨Li, Lo.adjoint, hLi, hRo,
    hc mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Lo.adjoint hLi hRo⟩

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
