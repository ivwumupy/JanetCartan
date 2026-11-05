module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CanonicalLocalizers

/-!
# Quantitative transport of the physical proof masks

The coordinate permutations used in `app:ch_regular:lem:finite-chain` preserve
the phase-space distance and every operator norm of a mask derivative. Thus
common physical shoulder widths and symbol constants remain common in all of
the factors' own canonical coordinates. This transport does not impose a
physical angular condition on canonical covectors.

Consumer: the coefficient-uniform protected-mask assembly in `Uniformity`.
The physical masks and their bounds still have to be constructed.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic FiniteChain.Graph

variable {d : ℕ}

/-- The actual coordinate permutation is an isometry for the physical
phase-space norm (`app:ch_regular:lem:finite-chain`). -/
def adaptedPhaseIsometry (i : Fin (d + 1)) :
    (Euclidean (d + 1) × Euclidean (d + 1)) ≃ₗᵢ[ℝ]
      (Euclidean (d + 1) × Euclidean (d + 1)) :=
  { (adaptedPhaseEquiv (coordinateSplit i)).toLinearEquiv with
    norm_map' := by
      intro p
      have hb := adaptedPhaseEquiv_covector_norm i (0, p.1)
      have hf := adaptedPhaseEquiv_covector_norm i p
      change ‖(adaptedPhaseEquiv (coordinateSplit i) p).1‖ = ‖p.1‖ at hb
      change ‖adaptedPhaseEquiv (coordinateSplit i) p‖ = ‖p‖
      rw [Prod.norm_def, Prod.norm_def, hb, hf] }

/-- All derivative orders retain the SAME bound under canonical pullback;
there is no coefficient-dependent multiplier or derivative loss
(`app:ch_regular:lem:finite-chain`, proof-mask grades). -/
theorem norm_iteratedFDeriv_canonicalProofLocalizer (i : Fin (d + 1))
    (m : LocalizerSymbol (d + 1)) (p : Euclidean (d + 1) × Euclidean (d + 1))
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (canonicalProofLocalizer (coordinateSplit i) m) p‖ =
      ‖iteratedFDeriv ℝ k m (adaptedPhaseEquiv (coordinateSplit i) p)‖ :=
  (adaptedPhaseIsometry i).norm_iteratedFDeriv_comp_right m p k

/-- A closed physical shoulder keeps its exact radius in every canonical
chart. The input is a bound on the already constructed physical plateau,
and the conclusion concerns its literal pullback
(`app:ch_regular:lem:finite-chain`). -/
theorem canonicalProofLocalizer_closedBall_plateau (i : Fin (d + 1))
    {m : LocalizerSymbol (d + 1)} {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    {δ : ℝ} (hbuffer : ∀ p ∈ S, closedBall p δ ⊆ interior {q | m q = 1}) :
    ∀ p ∈ adaptedPhaseEquiv (coordinateSplit i) ⁻¹' S,
      closedBall p δ ⊆ interior {q | canonicalProofLocalizer (coordinateSplit i) m q = 1} := by
  intro p hp q hq
  rw [plateau_canonicalProofLocalizer]
  apply hbuffer _ hp
  change dist (adaptedPhaseIsometry i q) (adaptedPhaseIsometry i p) ≤ δ
  rw [(adaptedPhaseIsometry i).dist_map]
  exact hq

/-- Common physical base-ball and annular bounds survive every chart's
canonical pullback, including the whole closed support
(`app:ch_regular:lem:finite-chain`). -/
theorem canonicalProofLocalizer_support_bounds (i : Fin (d + 1))
    {m : LocalizerSymbol (d + 1)} {R a b : ℝ}
    (hm : tsupport m ⊆ closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b) :
    tsupport (canonicalProofLocalizer (coordinateSplit i) m) ⊆
      closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b := by
  intro p hp
  rw [tsupport_canonicalProofLocalizer] at hp
  obtain ⟨hb, hf⟩ := hm hp
  have hn := adaptedPhaseEquiv_covector_norm i (0, p.1)
  change ‖(adaptedPhaseEquiv (coordinateSplit i) p).1‖ = ‖p.1‖ at hn
  simp only [mem_closedBall, dist_zero_right, hn] at hb
  change a ≤ ‖(adaptedPhaseEquiv (coordinateSplit i) p).2‖ ∧
    ‖(adaptedPhaseEquiv (coordinateSplit i) p).2‖ ≤ b at hf
  rw [adaptedPhaseEquiv_covector_norm] at hf
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hb, hf⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
