module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.CanonicalBounds

/-!
# Whole-segment envelopes and canonical support margins

For quantitative localization in `app:ch_regular:eq:chain-tail`, the proof
masks may protect the larger relation obtained by dropping only the two
amplitude-support restrictions. The original operators and their physical
amplitude factors are unchanged. Root-state buffers, whole segments, both
orientations and the original elapsed interval remain in this larger relation.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- Dropping amplitude-support restrictions enlarges only the relation used
to construct proof masks, not the physical operator
(`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_subset_unit_masks
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ : ℝ} {backward : Bool}
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward p q) :
    maskedZeroEnergyRelation e h Φ U K W (fun _ ↦ 1) (fun _ ↦ 1) Δ backward p q := by
  obtain ⟨r, hr, hc, _, _, hrel⟩ := hpq
  exact ⟨r, hr, hc, subset_closure (show (1 : ℂ) ≠ 0 from one_ne_zero),
    subset_closure (show (1 : ℂ) ≠ 0 from one_ne_zero), hrel⟩

/-- The finite union of actual physical relations lies in the same union
with unit amplitude masks. Both signs and orientations are preserved
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalDirectRelation_subset_unit_masks {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
    physicalDirectRelation i h Φ U K W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ p q := by
  obtain ⟨j, backward, a, b, hab, hp, hq⟩ := hpq
  exact ⟨j, backward, a, b, maskedZeroEnergyRelation_subset_unit_masks hab, hp, hq⟩

/-- The complete actual reachable sets, including diagonal branches, lie in
the unit-mask whole-segment envelope used for uniform gap construction
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalDirectRelation_reachableAt_subset_unit_masks {J : Type*}
    (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (n : ℕ) :
    reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S n ⊆
      reachableAt (physicalDirectRelation i h Φ U K W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ) S n := by
  rintro q ⟨p, hp, hc⟩
  refine ⟨p, hp, ?_⟩
  clear hp
  induction hc with
  | refl p => exact .refl p
  | tail hstep _ ih =>
    exact .tail (hstep.imp_right physicalDirectRelation_subset_unit_masks) ih

/-- Closed support shoulders commute with the actual canonical coordinate
permutation, with exactly the same radius (`app:ch_regular:eq:chain-tail`). -/
theorem cthickening_tsupport_canonicalProofLocalizer (i : Fin (d + 1))
    (m : LocalizerSymbol (d + 1)) (δ : ℝ) :
    cthickening δ (tsupport (canonicalProofLocalizer (coordinateSplit i) m)) =
      adaptedPhaseEquiv (coordinateSplit i) ⁻¹' cthickening δ (tsupport m) := by
  rw [tsupport_canonicalProofLocalizer]
  ext p
  change infEDist p (adaptedPhaseIsometry i ⁻¹' tsupport m) ≤ ENNReal.ofReal δ ↔
    infEDist (adaptedPhaseIsometry i p) (tsupport m) ≤ ENNReal.ofReal δ
  have he := infEDist_image (x := p)
    (t := adaptedPhaseIsometry i ⁻¹' tsupport m) (adaptedPhaseIsometry i).isometry
  rw [(adaptedPhaseIsometry i).surjective.image_preimage] at he
  rw [he]

/-- Transport both quantitative margins into a factor's own canonical
coordinates. In particular the input is the entire closed shoulder, and
the conclusion is a whole closed output ball, for either orientation
(`app:ch_regular:eq:chain-tail`). -/
theorem canonicalProofLocalizer_complete_image_closed_shoulder {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ δ : ℝ}
    {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ p ∈ cthickening δ (tsupport mi), ∀ q,
      p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        closedBall q δ ⊆ interior {q | mo q = 1})
    (j : J) (backward : Bool) {a b : Euclidean (d + 1) × Euclidean (d + 1)}
    (ha : a ∈ cthickening δ
      (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi)))
    (hab : a = b ∨ maskedZeroEnergyRelation (coordinateSplit (i j)) (h j) (Φ j)
      (U j) (K j) W (χsource j) (χout j) Δ backward a b) :
    closedBall b δ ⊆ interior {q | canonicalProofLocalizer (coordinateSplit (i j)) mo q = 1} := by
  rw [cthickening_tsupport_canonicalProofLocalizer] at ha
  have hb := hbuffer _ ha (adaptedPhaseEquiv (coordinateSplit (i j)) b) (by
    rcases hab with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr ⟨j, backward, a, b, hab, adaptedPhaseEquiv_apply _ _,
        adaptedPhaseEquiv_apply _ _⟩)
  intro q hq
  rw [plateau_canonicalProofLocalizer]
  apply hb
  change dist (adaptedPhaseIsometry (i j) q) (adaptedPhaseIsometry (i j) b) ≤ δ
  rwa [(adaptedPhaseIsometry (i j)).dist_map]

/-- The entire canonical closed shoulder retains the common physical base
and frequency bounds. Angular protection is still imposed only after the
physical coordinate conversion (`app:ch_regular:lem:finite-chain`). -/
theorem canonicalProofLocalizer_closed_shoulder_bounds (i : Fin (d + 1))
    {m : LocalizerSymbol (d + 1)} {δ R a b : ℝ}
    (hm : cthickening δ (tsupport m) ⊆
      closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b) :
    cthickening δ (tsupport (canonicalProofLocalizer (coordinateSplit i) m)) ⊆
      closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b := by
  intro p hp
  rw [cthickening_tsupport_canonicalProofLocalizer] at hp
  obtain ⟨hb, hf⟩ := hm hp
  have hn := adaptedPhaseEquiv_covector_norm i (0, p.1)
  change ‖(adaptedPhaseEquiv (coordinateSplit i) p).1‖ = ‖p.1‖ at hn
  simp only [mem_closedBall, dist_zero_right, hn] at hb
  change a ≤ ‖(adaptedPhaseEquiv (coordinateSplit i) p).2‖ ∧
    ‖(adaptedPhaseEquiv (coordinateSplit i) p).2‖ ≤ b at hf
  rw [adaptedPhaseEquiv_covector_norm] at hf
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hb, hf⟩

/-- Literal source recutting retains both positive margins and the original
outer plateau on `tsupport χ₂` (`app:ch_regular:lem:finite-chain`). The plateau
input is supplied by the paper's original nested source cutoffs. -/
theorem sourceRecutRelation_mem_closed_shoulder_plateau
    {R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    {mi mo : LocalizerSymbol (d + 1)} {δ : ℝ}
    (hbuffer : ∀ p ∈ cthickening δ (tsupport mi), ∀ q,
      p = q ∨ R p q → closedBall q δ ⊆ interior {q | mo q = 1})
    {χ₂ χ₃ : Euclidean (d + 1) → ℝ} (hcut : EqOn χ₃ 1 (tsupport χ₂))
    {p q : Euclidean (d + 1) × Euclidean (d + 1)}
    (hp : p ∈ cthickening δ (tsupport mi)) (hpq : sourceRecutRelation χ₂ R p q) :
    χ₃ p.1 = 1 ∧ closedBall q δ ⊆ interior {q | mo q = 1} :=
  ⟨sourceRecutRelation_outer_eq_one hcut hpq, hbuffer p hp q hpq.2⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
