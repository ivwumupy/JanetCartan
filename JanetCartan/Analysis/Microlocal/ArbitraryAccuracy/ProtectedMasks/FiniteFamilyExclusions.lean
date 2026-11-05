module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CanonicalExclusions
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.UniformCollar

/-!
# Exclusions on the actual finite total carrier

The total carrier includes both external bases, the three frequency variables,
elapsed time, the closed input shoulder and the entire output complement.
Its compactness uses a finite chart index and compact integration/base buffers,
not a compact class of current coefficients. The stationary exclusions below
are exactly the `hB` and `hI` inputs to
`exists_compactFamily_jointElapsedPhase_collar_data`.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ}

/-- The actual finite total carrier is compact and has no boundary or interior
stationary points after the constructed canonical masks. All chart identities
concern the SAME inverse flow chart and full supported segments. This supplies
the precise exclusions of `UniformCollar` without imposing compactness on a
varying coefficient class (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`).

The primitive carrier conditions come from the actual factor rectangles in
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`, restricted to both
physical factor supports. The physical buffer is the adjacent-pair conclusion
of `exists_nested_physicalDirectLocalizers_of_primitive_buffers`. -/
theorem compact_canonicalElapsedFamily_stationary_exclusions
    {J : Type*} [Finite J] [TopologicalSpace J]
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q,
      p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        q ∈ interior {q | mo q = 1})
    (C : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (hC : ∀ j, (C j : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (Φ j))
    (B : J → Set (Euclidean (d + 1) × Euclidean (d + 1)))
    (L : J → Set (ℝ × JointVariables (Euclidean (d + 1))))
    (hB : ∀ j, IsCompact (B j)) (hL : ∀ j, IsCompact (L j))
    (hqB : ∀ j rp, rp ∈ L j → elapsedChartPoint 0 rp.2.1.1 rp.2.2.1 ∈ (C j).target)
    (hiB : ∀ j rp, rp ∈ L j →
      Φ j (((C j).symm (elapsedChartPoint 0 rp.2.1.1 rp.2.2.1)).2, 0) =
        ((C j).symm (elapsedChartPoint 0 rp.2.1.1 rp.2.2.1)).2)
    (hphaseB : ∀ j rp, rp ∈ L j → HasFDerivAt (twoTimePhase (C j))
      (twoTimePhaseDifferential (h j) (Φ j) (C j) (elapsedChartPoint 0 rp.2.1.1 rp.2.2.1))
      (elapsedChartPoint 0 rp.2.1.1 rp.2.2.1))
    (hr : ∀ j rp, rp ∈ L j → rp.1 ∈ Icc 0 Δ)
    (hqI : ∀ j rp, rp ∈ L j → elapsedChartPoint rp.1 rp.2.1.1 rp.2.2.1 ∈ (C j).target)
    (hclock : ∀ j rp, rp ∈ L j →
      (twoTimeState (Φ j) ((C j).symm (elapsedChartPoint rp.1 rp.2.1.1 rp.2.2.1))).1 =
        rp.2.1.1 0)
    (hphaseI : ∀ j rp, rp ∈ L j → HasFDerivAt (twoTimePhase (C j))
      (twoTimePhaseDifferential (h j) (Φ j) (C j) (elapsedChartPoint rp.1 rp.2.1.1 rp.2.2.1))
      (elapsedChartPoint rp.1 rp.2.1.1 rp.2.2.1))
    (hsegment : ∀ j rp, rp ∈ L j →
      ((elapsedInputBase (C j) rp.1 rp.2.1.1 rp.2.2.1, rp.2.2.1), rp.1) ∈
        elapsedSegmentCarrier (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W)
    (hs : ∀ j rp, rp ∈ L j → rp.2.1.2 ∈ tsupport (χsource j))
    (ho : ∀ j rp, rp ∈ L j → rp.2.1.1 ∈ tsupport (χout j)) :
    let T := elapsedFiniteFamilyCarrier B L
      (fun j ↦ canonicalProofLocalizer (coordinateSplit (i j)) mi)
      (fun j ↦ canonicalProofLocalizer (coordinateSplit (i j)) mo)
    IsCompact T ∧ ∀ backward : Bool,
      (∀ t ∈ T, fderiv ℝ (fun p ↦
        jointElapsedPhase backward (chartPhase (C t.1.1)) t.1.2.1 t.1.2.2 (0, p)) t.2.2 ≠ 0) ∧
      (∀ t ∈ T, 0 < t.2.1 → fderiv ℝ
        (jointElapsedPhase backward (chartPhase (C t.1.1)) t.1.2.1 t.1.2.2) t.2 ≠ 0) := by
  refine ⟨isCompact_elapsedFiniteFamilyCarrier B L _ _ hB hL, ?_⟩
  intro backward
  constructor
  · intro t ht
    exact fderiv_jointElapsedPhase_boundary_ne_zero_of_physical_buffer hbuffer t.1.1
      (hC t.1.1) backward t.1.2.1 t.1.2.2 t.2.2
      (hqB _ _ ht.2.1) (hiB _ _ ht.2.1) (hphaseB _ _ ht.2.1) ht.2.2.1 ht.2.2.2
  · intro t ht _
    exact fderiv_jointElapsedPhase_ne_zero_of_physical_buffer hbuffer t.1.1
      (hC t.1.1) backward t.1.2.1 t.1.2.2 (hr _ _ ht.2.1) t.2.2
      (hqI _ _ ht.2.1) (hclock _ _ ht.2.1) (hphaseI _ _ ht.2.1)
      (hsegment _ _ ht.2.1) (hs _ _ ht.2.1) (ho _ _ ht.2.1) ht.2.2.1 ht.2.2.2

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
