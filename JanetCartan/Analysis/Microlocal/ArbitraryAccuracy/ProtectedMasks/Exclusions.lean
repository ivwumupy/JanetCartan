module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations

/-!
# Stationary exclusions for the complete masked relation

The geometric input is a support-to-open-plateau inclusion for the ACTUAL
masked relation, rather than an unrestricted fixed-elapsed graph. At a
stationary point the two physical positions and source covector identify
the literal factor masks and the complete segment carrier. Hence the full
closed input shoulders and the full complementary output support are covered.

Consumers: `EvolutionIntegratedLocalization.GradientGaps` and `UniformCollar`
in `app:ch_regular:eq:chain-tail`. The nested-mask producer must still supply
the buffer; these implications do not assert that it has been constructed.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ}

/-- The actual stationary equations identify the original source and both
factor positions, including for the literal adjoint. The original source
covector is the phase covector, rather than the adjoint input covector
(`app:ch_regular:eq:joint-stationary`). -/
theorem stationary_original_positions
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (backward : Bool) (x y : Euclidean (d + 1)) (r : ℝ)
    (p : JointVariables (Euclidean (d + 1)))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hz : fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) = 0) :
    originalSource backward (y, p.2.2.1) (x, p.2.2.2) =
        (elapsedInputBase C r p.1.1 p.2.1, p.2.1) ∧
      (originalSource backward (y, p.2.2.1) (x, p.2.2.2)).1 = p.1.2 ∧
      (originalTarget backward (y, p.2.2.1) (x, p.2.2.2)).1 = p.1.1 := by
  cases backward
  · have hs := (fderiv_jointElapsedPhase_forward_eq_zero_iff x y r p hphase).mp hz |>.1
    obtain ⟨_, hη, hb, hy, hx⟩ :=
      (forwardStationary_elapsed_iff r x y _ _ _ _ _ hphase).mp hs
    exact ⟨Prod.ext (hy.symm.trans hb) hη, hy.symm, hx⟩
  · have hs := (fderiv_jointElapsedPhase_reverse_eq_zero_iff x y r p hphase).mp hz |>.1
    obtain ⟨_, hζ, hb, hy, hx⟩ :=
      (reverseStationary_elapsed_iff r x y _ _ _ _ _ hphase).mp hs
    exact ⟨Prod.ext (hx.trans hb) hζ, hx, hy.symm⟩

/-- An actual interior critical point belongs to the supported zero-energy
relation. Whole-domain data concern the inverse-chart source, while the
physical masks concern the original integration positions; the stationary
equations prove their identification (`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_of_stationary
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (backward : Bool) (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hsegment : ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier e h Φ U K W)
    (hs : p.1.2 ∈ tsupport χsource) (ho : p.1.1 ∈ tsupport χout)
    (hz : fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) = 0) :
    maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward
      (y, p.2.2.1) (x, p.2.2.2) := by
  obtain ⟨hsource, hspos, hopos⟩ := stationary_original_positions backward x y r p hphase hz
  refine ⟨r, hr, ?_, ?_, ?_,
    zeroEnergyFlowRelation_of_stationary hC backward x y r p hq hclock hphase hz⟩
  · rwa [hsource]
  · rwa [hspos]
  · rwa [hopos]

/-- Exclude the full interior stationary set on the closed source shoulders
and the ENTIRE complementary output support. Only images surviving the actual
physical masks and whole segment domains require protection. This supplies
`hI` of `exists_compactFamily_jointElapsedPhase_collar_data` once the nested
masks are constructed (`app:ch_regular:eq:chain-tail`). -/
theorem fderiv_jointElapsedPhase_ne_zero_of_masked_buffer
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ : ℝ}
    (backward : Bool) {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ a ∈ tsupport mi, ∀ b,
      maskedZeroEnergyRelation e h Φ U K W χsource χout Δ backward a b →
        b ∈ interior {q | mo q = 1})
    (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hsegment : ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier e h Φ U K W)
    (hs : p.1.2 ∈ tsupport χsource) (ho : p.1.1 ∈ tsupport χout)
    (hin : (y, p.2.2.1) ∈ tsupport mi)
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p) ≠ 0 := by
  intro hz
  exact notMem_complement_tsupport_of_mem_plateau
    (hbuffer _ hin _ (maskedZeroEnergyRelation_of_stationary e hC backward x y hr p
      hq hclock hphase hsegment hs ho hz)) hout

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
