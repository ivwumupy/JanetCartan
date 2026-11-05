module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.Localizers

/-!
# Protection of the literal direct relations

Derive the physical angular conclusion from the common pencil roots and the
SAME comparison charts and source cover retained by initialized protection.
The coordinate-pairing input is discharged for the actual coordinate split.
The annular cutoff lemma concerns a compact protected set; compactness and
uniform neighborhoods of the actual reachable sets are separate obligations
of the nested-mask construction, not assumptions of the chain protection.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ} {I J : Type*}

/-- The retained angular buffer protects every actual direct chain. The
source cover, conic-family buffer, and characteristic-chain result are the
literal outputs of `exists_initialized_signed_no_return` for the SAME `Q`.
The last is used only at length zero to handle elliptic sources. No direct
chain protection or coordinate-pairing premise is added
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem physicalDirectRelation_chain_angular_buffer
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q)
    (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
        ((coordinateSplit (i j)).symm (h j v, v.2.2))
        ((coordinateSplit (i j)).symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean (d + 1))}
    (C : (j : I) → ComparisonChart
      (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j))
    {r ε : ℝ} (hradius : ∀ j, 2 * r < (g j).radius)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    {G : Set (Euclidean (d + 1))}
    (hcover : ∀ z ∈ S, normalizedSymbol Q z = 0 →
      z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hbuffer : ∀ z ∈ positiveConicLift (ComparisonChart.familyGradient C)
      (ball 0 (2 * r)) univ, closedBall (normalizedCovector z.2) ε ⊆ G)
    (hretained : ∀ z ∈ S, ∀ w k,
      PositiveConicChain (CompleteCharacteristicSegment
        (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (ball 0 (2 * r)))
        z w k → closedBall (normalizedCovector w.2) ε ⊆ G)
    {z w : Euclidean (d + 1) × Euclidean (d + 1)} {k : ℕ} (hz : z ∈ S)
    (hc : PositiveConicChain
      (physicalDirectRelation i h Φ U K (ball 0 (2 * r)) χsource χout Δ) z w k) :
    closedBall (normalizedCovector w.2) ε ⊆ G := by
  exact pencilRoot_chain_angular_buffer (fun j ↦ coordinateSplit (i j))
    (fun j ↦ coordinateSplit_inverse_pairing (i j)) hQ hD hh hroot C hradius
    hcover hbuffer (retained_source_angular_buffer hretained) hz
    (physicalDirectRelation_chain i h Φ U K D _ χsource χout Δ hKD hi hode hc)

/-- Nonzero output covectors follow from the root domains and the original
source, also along diagonal steps (`app:ch_regular:lem:finite-chain`). -/
theorem physicalDirectRelation_chain_covector_ne_zero
    (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hne : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0)
    {z w : Euclidean (d + 1) × Euclidean (d + 1)} {k : ℕ}
    (hc : PositiveConicChain (physicalDirectRelation i h Φ U K W χsource χout Δ) z w k)
    (hz : z.2 ≠ 0) : w.2 ≠ 0 :=
  pencilRoot_chain_covector_ne_zero (fun j ↦ coordinateSplit (i j)) hne
    (physicalDirectRelation_chain i h Φ U K D W χsource χout Δ hKD hi hode hc) hz

/-- Elliptic sources have only identity branches for the actual masked
relation. Their physical covector is therefore unchanged
(`app:ch_regular:thm:no-return`). -/
theorem elliptic_physicalDirectRelation_chain_eq
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hroot : ∀ j, ∀ v ∈ D j,
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0)
    {z w : Euclidean (d + 1) × Euclidean (d + 1)} {k : ℕ}
    (hc : PositiveConicChain (physicalDirectRelation i h Φ U K W χsource χout Δ) z w k)
    (hz : normalizedSymbol Q z ≠ 0) : z = w :=
  elliptic_pencilRoot_chain_eq (fun j ↦ coordinateSplit (i j)) hroot
    (physicalDirectRelation_chain i h Φ U K D W χsource χout Δ hKD hi hode hc) hz

/-- The final physical mask is supported strictly inside the retained angular
set, away from zero covectors. Intermediate canonical masks are not required
to satisfy this physical condition (`app:ch_regular:lem:finite-chain`). -/
def physicalProtectedRegion (Γ : Set (Euclidean (d + 1))) :
    Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  {p | p.2 ≠ 0 ∧ normalizedCovector p.2 ∈ interior Γ}

/-- The protected physical target is open, permitting closed mask shoulders
strictly inside it (`app:ch_regular:lem:finite-chain`). -/
theorem isOpen_physicalProtectedRegion (Γ : Set (Euclidean (d + 1))) :
    IsOpen (physicalProtectedRegion Γ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hn := (isOpen_ne_fun continuous_snd continuous_const).mem_nhds hp.1
  have hc : ContinuousAt (fun q : Euclidean (d + 1) × Euclidean (d + 1) ↦
      normalizedCovector q.2) p := by
    exact (continuous_snd.norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hp.1)).smul
      continuous_snd.continuousAt
  filter_upwards [hn, hc.preimage_mem_nhds (isOpen_interior.mem_nhds hp.2)] with q hq hΓ
  exact ⟨hq, hΓ⟩

/-- A compact protected image has a smooth final mask with positive lower
and finite upper frequency bounds on its ENTIRE closed support. This is a
cutoff construction, not an assertion that an arbitrary reachable image is
compact. The relation compactness and nesting are separate obligations
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_physicalProtectedLocalizer
    {K : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    {Γ : Set (Euclidean (d + 1))} (hK : IsCompact K)
    (hne : ∀ p ∈ K, p.2 ≠ 0)
    (hang : ∀ p ∈ K, normalizedCovector p.2 ∈ interior Γ) :
    ∃ (m : LocalizerSymbol (d + 1)) (B : Set (Euclidean (d + 1))) (a b : ℝ),
      IsBufferedLocalizer m K (physicalProtectedRegion Γ) ∧
      IsCompact B ∧ 0 < a ∧ a < b ∧
      tsupport m ⊆ B ×ˢ PhysicalShells.frequencyAnnulus a b := by
  obtain ⟨m, hm, hr, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff hK
    (isOpen_physicalProtectedRegion Γ) (fun p hp ↦ ⟨hne p hp, hang p hp⟩)
  have hmask : IsBufferedLocalizer m K (physicalProtectedRegion Γ) := ⟨hm, hr, hc, hs, hp⟩
  obtain ⟨B, a, b, hB, ha, hab, hsupport⟩ :=
    EvolutionLocalization.exists_elapsed_localizer_annular_carrier hmask (fun _ hp ↦ hp.1)
  exact ⟨m, B, a, b, hmask, hB, ha, hab, hsupport⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
