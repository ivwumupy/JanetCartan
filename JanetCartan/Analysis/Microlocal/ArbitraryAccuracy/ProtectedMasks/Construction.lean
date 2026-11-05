module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.FiniteFamilyExclusions

/-!
# Assembly from the actual smooth root flows

The finite-depth construction uses the common-domain smooth flows produced by
`UniformGeometry`, the SAME retained initialized protection, and the selected
compact initial and whole-segment buffers. It discharges the flow continuity,
initial-value and ambient ODE hypotheses of the nesting construction. The
physical masks are then pulled into each factor's own canonical coordinates.
The closed whole-segment buffer sits inside the open comparison ball; the
original elapsed bound is unchanged at every depth.

This is a fixed-family geometric construction. Uniform mask/gap constants over
varying current coefficients remain separate from the actual current-family
instantiation retained by the arbitrary-accuracy parent.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open FiniteChain.Graph

variable {d : ℕ}

/-- Finite nested masks from the actual common root flows and retained
comparison family, including depth zero. The first closed shoulder stays in
the prescribed source buffer, both oriented zero-energy relations and the full
diagonal map into the next open plateau, and every canonical mask is compact
and annular. The final physical mask lies strictly inside the retained angular
region (`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph).

The actual primitive producer is
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`; it supplies the
`IsSmoothFlowOn` fields used here. The comparison/source inputs come from
`ProtectedFlow.exists_initialized_signed_no_return` for the SAME pencil.
There is no mask, direct-chain image inclusion, pairing, compact-graph or
stationary-exclusion assumption. For stationary exclusions on the literal
factor carriers, apply `compact_canonicalElapsedFamily_stationary_exclusions`
to the adjacent-mask conclusion. All choices precede requested accuracy. -/
theorem exists_nested_canonicalDirectLocalizers {I J : Type*} [Finite J]
    (i : J → Fin (d + 1))
    {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1)}
    (hQ : ContDiff ℝ ∞ Q)
    (h : J → RootState (Euclidean d) → ℝ)
    (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
    (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ)
    (hKD : ∀ j, K j ⊆ D j)
    (z : J → RootState (Euclidean d)) (R rFlow T : J → ℝ)
    (hflow : ∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
      (z j) (R j) (rFlow j) (T j) (Φ j))
    (hT : ∀ j, 0 < T j) (hΔ : ∀ j, Δ < T j)
    (hUflow : ∀ j, U j ⊆ closedBall (z j) (rFlow j))
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
    (hWball : W ⊆ ball 0 (2 * r))
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
    (hε : 0 < ε) (hS : IsCompact S) (hSnonzero : ∀ z ∈ S, z.2 ≠ 0)
    {Bsource : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hBsource : IsOpen Bsource) (hSBsource : S ⊆ Bsource)
    (hU : ∀ j, IsCompact (U j)) (hK : ∀ j, IsCompact (K j))
    (hW : IsClosed W) (hUD : ∀ j, U j ⊆ D j)
    (N : ℕ) :
    ∃ (m : Fin (N + 1) → LocalizerSymbol (d + 1))
      (Bfinal : Set (Euclidean (d + 1))) (a b : ℝ),
      (∀ j, IsBufferedLocalizer (m j)
        (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ)
          S j.val) (physicalProtectedRegion G)) ∧
      IsBufferedLocalizer (m 0) S Bsource ∧
      (∀ j : Fin N, ∀ p ∈ tsupport (m j.castSucc), ∀ q,
        p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        q ∈ interior {q | m j.succ q = 1}) ∧
      IsCompact Bfinal ∧ 0 < a ∧ a < b ∧
      tsupport (m (Fin.last N)) ⊆ Bfinal ×ˢ PhysicalShells.frequencyAnnulus a b ∧
      (∀ k j, IsBufferedLocalizer (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹'
          reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
        (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion G)) ∧
      (∀ (k : Fin N) j backward, ∀ p ∈ tsupport
        (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc)), ∀ q,
        p = q ∨ maskedZeroEnergyRelation (coordinateSplit (i j)) (h j) (Φ j)
          (U j) (K j) W (χsource j) (χout j) Δ backward p q →
          q ∈ interior {q | canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q = 1}) ∧
      (∀ k j, ∃ (B : Set (Euclidean (d + 1))) (a b : ℝ),
        IsCompact B ∧ 0 < a ∧ a < b ∧
        tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
          B ×ˢ PhysicalShells.frequencyAnnulus a b) := by
  have hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v :=
    fun j v hv ↦ (hflow j).initial v (hUflow j hv)
  have hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t := by
    intro j v hv t ht
    exact (hflow j).hasDerivAt (hUflow j hv)
      ⟨(neg_neg_of_pos (hT j)).trans_le ht.1, ht.2.trans_lt (hΔ j)⟩
  have hΦ : ∀ j, ContinuousOn (Φ j) (U j ×ˢ Icc 0 Δ) := by
    intro j
    apply (hflow j).continuous.mono
    intro p hp
    exact ⟨hUflow j hp.1, (neg_nonpos.mpr (hT j).le).trans hp.2.1,
      hp.2.2.trans (hΔ j).le⟩
  obtain ⟨m, Bfinal, a, b, hm, hfirst, hnest, hBfinal, ha, hab, hsupport⟩ :=
    exists_nested_physicalDirectLocalizers_of_primitive_buffers i hQ h Φ U K D W χsource χout Δ
      hKD hi hode hD hh hroot C hradius hWball hcover hbuffer hretained hε hS hSnonzero
      hBsource hSBsource hU hK hW hUD hΦ N
  have hcanonical k j := IsBufferedLocalizer.canonicalProofLocalizer
    (coordinateSplit (i j)) (hm k)
  refine ⟨m, Bfinal, a, b, hm, hfirst, hnest, hBfinal, ha, hab, hsupport,
    hcanonical, ?_, ?_⟩
  · intro k j backward p hp q hpq
    exact canonicalProofLocalizer_complete_image (hnest k) j backward hp hpq
  · intro k j
    apply EvolutionLocalization.exists_elapsed_localizer_annular_carrier (hcanonical k j)
    intro p hp hz
    have hne := hp.1
    have hnorm := adaptedPhaseEquiv_covector_norm (i j) p
    rw [hz, norm_zero] at hnorm
    exact hne (norm_eq_zero.mp hnorm)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
