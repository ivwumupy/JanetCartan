module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CanonicalLocalizers

/-!
# Stationary exclusions for the constructed canonical masks

The physical adjacent-mask buffer comes from
`exists_nested_physicalDirectLocalizers_of_primitive_buffers`. Pulling it back
supplies exactly the boundary and interior exclusions used by
`EvolutionIntegratedLocalization.GradientGaps` and `UniformCollar`.
The entire closed input support and output complement occur in each statement.
The interior retains both actual amplitude masks and every segment point;
the boundary retains the full diagonal without an energy restriction.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ} {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q,
      p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        q ∈ interior {q | mo q = 1})
    (j : J)
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection (Φ j))
    (backward : Bool)

include hbuffer hC

/-- Interior full-gradient exclusion in each actual chart, for either
orientation, including every input shoulder and the identity contribution
of the output complement (`app:ch_regular:eq:chain-tail`). -/
theorem fderiv_jointElapsedPhase_ne_zero_of_physical_buffer
    (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState (Φ j) (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential (h j) (Φ j) C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hsegment : ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W)
    (hs : p.1.2 ∈ tsupport (χsource j)) (ho : p.1.1 ∈ tsupport (χout j))
    (hin : (y, p.2.2.1) ∈ tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi))
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q)) :
    fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) ≠ 0 := by
  apply fderiv_jointElapsedPhase_ne_zero_of_masked_buffer (coordinateSplit (i j))
    hC backward (fun a ha b hab ↦ canonicalProofLocalizer_complete_image hbuffer j backward
      ha (Or.inr hab)) x y hr p hq hclock hphase hsegment hs ho hin hout

/-- Boundary tangential-gradient exclusion for the same canonical masks.
This uses the entire diagonal, including elliptic identity branches, and
makes no zero-energy assumption (`app:ch_regular:eq:chain-tail`). -/
theorem fderiv_jointElapsedPhase_boundary_ne_zero_of_physical_buffer
    (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target)
    (hi : Φ j ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
      (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential (h j) (Φ j) C (elapsedChartPoint 0 p.1.1 p.2.1))
      (elapsedChartPoint 0 p.1.1 p.2.1))
    (hin : (y, p.2.2.1) ∈ tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi))
    (hout : (x, p.2.2.2) ∈ tsupport
      (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q)) :
    fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p ≠ 0 := by
  apply fderiv_jointElapsedPhase_boundary_ne_zero_of_buffer hC backward
    (fun a ha ↦ canonicalProofLocalizer_complete_image hbuffer j backward ha (Or.inl rfl))
    x y p hq hi hphase hin hout

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
