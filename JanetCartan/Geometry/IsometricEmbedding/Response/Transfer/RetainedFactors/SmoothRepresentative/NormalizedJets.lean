module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative.Jets

/-!
# Uniform normalized elapsed jets of the actual smooth representative

The fixed positive spatial lower bound removes the transition at every
scale `R ≥ 1`. Joint germ agreement then transfers the existing quantitative
elapsed estimate from the original phase. All constants precede the phase,
scale and elapsed time; localization has derivative shift zero.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
open RegularSector.Characteristic ConicPhase EvolutionIntegral FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Frequency normalization preserves joint germ agreement uniformly above
the one fixed transition (`app:ch_response:eq:direct-envelope-profile`). -/
theorem normalized_elapsed_representative_eventuallyEq
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ} {K : Set T}
    (he : ∀ q ∈ K, χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    {t R : ℝ} (hR : 1 ≤ R) {p : E × E}
    (hp : (p.1 0, (p.1 0 - t, (spatialPart p.1, spatialPart p.2))) ∈ domain ℓ K)
    (hfreq : δ ≤ ‖spatialPart p.2‖) :
    Function.uncurry (WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t)) =ᶠ[𝓝 p]
    Function.uncurry (WholeImageGeometry.normalizedPhase R (elapsedPhase (curriedPhase ℓ C) t)) := by
  have hpos := zero_lt_one.trans_le hR
  have hp' : (p.1 0, (p.1 0 - t, (spatialPart p.1, spatialPart (R • p.2)))) ∈
      domain ℓ K := by
    rw [SymbolBudgets.spatialPart_smul]
    exact mem_domain_smul ℓ hp hpos
  have hf' : δ ≤ ‖spatialPart (R • p.2)‖ := by
    rw [SymbolBudgets.spatialPart_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact hfreq.trans (le_mul_of_one_le_left (norm_nonneg _) hR)
  have hg := elapsed_representative_eventuallyEq ℓ C hδ he hp' hf'
  have hc : Continuous (fun q : E × E ↦ (q.1, R • q.2)) :=
    continuous_fst.prodMk (continuous_snd.const_smul R)
  filter_upwards [hg.comp_tendsto (hc.tendsto p)] with q hq
  exact congrArg (fun a : ℝ ↦ R⁻¹ * a) hq

/-- The existing original-buffer estimate supplies every normalized elapsed
jet of the constructed smooth representative. There is no assumed extended
phase budget, and the derivative shift is zero. The coefficient producer's
original `n+1` phase reserve is therefore unchanged
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_iteratedFDeriv_buffered_normalized_representative_le
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    {δ : ℝ} (hδ : 0 < δ) {χ : T → ℝ}
    {z : RootState (Euclidean d)} {ε a b τ : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (he : ∀ q ∈ closedBall (z.1, z) (2 * ε), χ =ᶠ[𝓝 q] (fun _ ↦ 1))
    (hbuffer : closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {R t : ℝ} (hR : 1 ≤ R) (ht : t ∈ Icc 0 ε)
    {n k : ℕ} (hk : k ≤ n) {p : E × E}
    (hp : SymbolBudgets.phasePairInclusion p ∈ elapsedJetSet ℓ z ε a b τ)
    (hfreq : δ ≤ ‖spatialPart p.2‖) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (WholeImageGeometry.normalizedPhase R
      (elapsedPhase (curriedRepresentative ℓ δ hδ χ (twoTimePhase C)) t))) p‖ ≤
        SymbolBudgets.phaseTimeConstant (elapsedJetSet ℓ z ε a b τ) n ε +
          jetBoundConstant ℓ (budgetCoordinates '' bufferedJetSet ℓ z ε a b) n *
            cNorm (closedBall (z.1, z) (2 * ε)) n (twoTimePhase C) := by
  have hm := elapsedJetSet_mapsTo ℓ ht hp
  have hn := bufferedJetSet_normalizes ℓ (z := z) (b := b) hε ha
  have hd : (p.1 0, (p.1 0 - t, (spatialPart p.1, spatialPart p.2))) ∈
      domain ℓ (closedBall (z.1, z) (2 * ε)) := by
    have hh := And.intro (hn.1 _ hm) (hn.2 hm)
    simpa [SymbolBudgets.phasePairInclusion, budgetCoordinates, domain] using hh
  have heq := normalized_elapsed_representative_eventuallyEq ℓ C hδ he hR
    (t := t) (p := p) hd hfreq
  have hj := (heq.iteratedFDeriv ℝ k).eq_of_nhds
  rw [hj]
  exact norm_iteratedFDeriv_buffered_elapsed_le ℓ hε ha C.open_target hbuffer hC
    (zero_lt_one.trans_le hR) ht hk hp

end JanetCartan.ResponseTransfer.RetainedFactors.SmoothRepresentative
