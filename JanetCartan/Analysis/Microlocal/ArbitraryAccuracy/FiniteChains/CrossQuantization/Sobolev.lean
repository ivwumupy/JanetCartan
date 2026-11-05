module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.FourierAction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.BufferedDecay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Sobolev.Endpoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.BoundedLocalizers

/-!
# The forward cross-quantization Sobolev estimate

The literal Fourier action and the buffered primitive-data kernel estimate
give the all-L² bound for `(1 - Ro).comp Li`. Its fixed loss is
`m + (n + 1) + (bo + bi)`, independent of accuracy. The constants precede
the varying symbols and scales, and the same operators work for every `N`.

This supplies the forward cross-quantization input connecting `CompleteFactor`
to `finiteChain_observation_rapidDecayAt` in `app:ch_regular:lem:finite-chain`
and `app:ch_regular:eq:chain-tail`. The parent retains the literal-adjoint
instantiation and the final finite-chain assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Uniform forward cross-quantization estimate from the original primitive
mask data. The bounded maps are fixed before `N` and are identified only by
their literal left and right actions, supplied by
`exists_bounded_physicalLocalizers`. The proof instantiates both the checked
Fourier action and the checked buffered kernel bound, proving output Sobolev
membership for every L² input (`app:ch_regular:eq:chain-tail`). -/
theorem exists_crossQuantization_sobolev_bound
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
      ∀ N (u : H), MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li) u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li) u) ≤
          C N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨S, hS, hs⟩ := exists_channelFourierKernel_sobolev_constant (n := n) (r := r) m
  obtain ⟨C, hC, hc⟩ := exists_crossQuantizationFourierKernel_weighted_decay
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
      (Function.uncurry (crossQuantizationFourierKernel ρ mi mo)) :=
    (contDiff_crossQuantizationFourierKernel ρ mi mo hi his ho).continuous.stronglyMeasurable
  have hb (ξ η : E) : (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) *
      ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ ≤ B := by
    calc
      _ ≤ ((1 + ‖ξ‖) ^ m + (1 + ‖η‖) ^ m) * (1 + ‖ξ - η‖) ^ (n + 1) *
          ‖crossQuantizationFourierKernel ρ mi mo ξ η‖ := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
      _ ≤ B := hc mi mo hi ho hcarrier hann hbuffer ρ L hL hLρ hij hoj N ξ η
  have h := hs (crossQuantizationFourierKernel ρ mi mo) hk B hB hb
    ((1 - Ro).comp Li)
    (bounded_crossQuantization_schwartz_fourier_action hρ.ne' mi mo hi his ho hos Li Ro hLi hRo) u
  refine ⟨h.1, ?_⟩
  simpa only [B, mul_assoc] using h.2

/-- Construct bounded left and right proof localizers and prove the forward
cross estimate from primitive data, with no realization premise left to
discharge. Both operators are selected before accuracy and work for all `N`.
The constants and fixed loss are those of
`exists_crossQuantization_sobolev_bound`. Consumer: the forward bridge from
`CompleteFactor` to `finiteChain_observation_rapidDecayAt`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_bounded_crossQuantization_sobolev_bound
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
      ∃ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) ∧
      ∀ N (u : H), MemVectorFourierSobolev (m : ℝ) (((1 - Ro).comp Li) u) ∧
        vectorFourierSobolevNorm (m : ℝ) (((1 - Ro).comp Li) u) ≤
          C N * ρ ^ m * L ^ (m + (n + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨C, hC, hc⟩ := exists_crossQuantization_sobolev_bound
    (r := r) K hK Di Do hDi hDo bi bo hδ hR m
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
