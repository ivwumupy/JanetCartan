module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap.Endpoints
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap.ConicTransfer
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Margins

/-!
# A coefficient-independent interior gradient gap

The quantitative mask margin constructed by
`exists_uniform_nested_physicalDirectLocalizers` gives the interior gap
of `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.
The gap is chosen from the margin and a fixed integration-variable basis
before the coefficients, flow, chart, external bases and integration point.

The entire closed input shoulder and full complementary output support
are retained. The mask premise protects the larger unit-amplitude relation;
the actual amplitude factors in the operators are unchanged. Its actual
instantiation belongs to the final coefficient-uniform localization assembly.

`InteriorGap.ConicTransfer` transfers this gap to the actual normalized
conic phase and its supported replacements. The parent must verify the
stated overlap and supported germs on its actual integration support.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization

variable {d : ℕ}

/-- Quantitative interior separation in one factor's canonical coordinates.
The exact whole-segment mask margin is transported from physical coordinates
by `canonicalProofLocalizer_complete_image_closed_shoulder`.
Consumer: the coefficient-uniform squared-gradient gap for
`app:ch_regular:eq:chain-tail`. -/
theorem norm_fderiv_jointElapsedPhase_ge_of_closed_shoulder
    {θ : ℝ} (hθ : 0 < θ)
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))} {Δ : ℝ}
    {mi mo : LocalizerSymbol (d + 1)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool)
    (hbuffer : ∀ a ∈ cthickening θ (tsupport mi), ∀ b,
      maskedZeroEnergyRelation e h Φ U K W (fun _ ↦ 1) (fun _ ↦ 1) Δ backward a b →
        closedBall b θ ⊆ interior {q | mo q = 1})
    (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint r p.1.1 p.2.1 ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r p.1.1 p.2.1))
      (elapsedChartPoint r p.1.1 p.2.1))
    (hsegment : ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier e h Φ U K W)
    (hin : (y, p.2.2.1) ∈ cthickening (θ / 2) (tsupport mi))
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    θ / 6 ≤ ‖fderiv ℝ (jointElapsedPhase backward (chartPhase C) x y) (r, p)‖ := by
  by_contra! hsmall
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_nearby_maskedZeroEnergyRelation hC backward x y hr p hq hclock hphase hsegment
  have hinput : a ∈ cthickening θ (tsupport mi) := by
    have hnear : a ∈ cthickening (θ / 2) (cthickening (θ / 2) (tsupport mi)) :=
      mem_cthickening_of_dist_le _ _ _ _ hin (by rw [dist_comm]; linarith)
    have hsum := cthickening_cthickening_subset (by positivity : 0 ≤ θ / 2)
      (by positivity : 0 ≤ θ / 2) (tsupport mi) hnear
    simpa only [add_halves] using hsum
  exact notMem_complement_tsupport_of_mem_plateau
    (hbuffer a hinput b hab (by change dist (x, p.2.2.2) b ≤ θ; linarith)) hout

private theorem exists_phaseGradientSquare_gap_of_norm_gap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {κ : Type*} [Fintype κ] (e : Module.Basis κ ℝ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : V → ℝ) (p : V), ε ≤ ‖fderiv ℝ F p‖ →
      δ ≤ phaseGradientSquare e F p := by
  obtain ⟨B, hB, hbound⟩ := e.exists_opNorm_le (F := ℝ)
  let M := ε / (2 * B)
  have hM : 0 < M := div_pos hε (by positivity)
  refine ⟨M ^ 2, sq_pos_of_pos hM, ?_⟩
  intro F p hnorm
  by_contra! hsmall
  have heval (k : κ) : ‖fderiv ℝ F p (e k)‖ ≤ M := by
    have hs : (fderiv ℝ F p (e k)) ^ 2 ≤ phaseGradientSquare e F p :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (fderiv ℝ F p (e j))) (Finset.mem_univ k)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (fderiv ℝ F p (e k)), abs_nonneg (fderiv ℝ F p (e k))]
  have hn := hbound hM.le heval
  have hBM : B * M = ε / 2 := by dsimp [M]; field_simp
  rw [hBM] at hn
  linarith

/-- Choose the interior squared-gradient gap BEFORE all coefficients,
flows, charts, masks, external bases, integration variables and orientations.
Its only geometric input is the actual quantitative unit-mask margin from
`exists_uniform_nested_physicalDirectLocalizers`; its coordinate transport is
`canonicalProofLocalizer_complete_image_closed_shoulder`.
The chart and segment hypotheses are precisely the restrictions used in
`CanonicalExclusions`, supplied by `UniformGeometry` and its `RootFlow` leaf.
Consumer: the final coefficient-uniform localization assembly for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`. -/
theorem exists_uniform_interior_phaseGradientSquare_gap
    {J κ : Type*} [Fintype κ] {θ : ℝ} (hθ : 0 < θ)
    (eI : Module.Basis κ ℝ (ℝ × JointVariables (Euclidean (d + 1)))) :
    ∃ δI > 0,
    ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
      (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
      (Δ : ℝ) (mi mo : LocalizerSymbol (d + 1)),
      (∀ a ∈ cthickening θ (tsupport mi), ∀ b,
        a = b ∨ physicalDirectRelation i h Φ U K W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ a b →
          closedBall b θ ⊆ interior {q | mo q = 1}) →
    ∀ (j : J)
      (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
      (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection (Φ j) →
    ∀ (backward : Bool) (x y : Euclidean (d + 1)) (r : ℝ), r ∈ Icc 0 Δ →
    ∀ (p : JointVariables (Euclidean (d + 1))),
      elapsedChartPoint r p.1.1 p.2.1 ∈ C.target →
      (twoTimeState (Φ j) (C.symm (elapsedChartPoint r p.1.1 p.2.1))).1 = p.1.1 0 →
      HasFDerivAt (twoTimePhase C)
        (twoTimePhaseDifferential (h j) (Φ j) C (elapsedChartPoint r p.1.1 p.2.1))
        (elapsedChartPoint r p.1.1 p.2.1) →
      ((elapsedInputBase C r p.1.1 p.2.1, p.2.1), r) ∈
        elapsedSegmentCarrier (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W →
      (y, p.2.2.1) ∈ cthickening (θ / 2)
        (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi)) →
      (x, p.2.2.2) ∈ tsupport
        (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q) →
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward (chartPhase C) x y) (r, p) := by
  obtain ⟨δI, hδI, hgap⟩ := exists_phaseGradientSquare_gap_of_norm_gap eI
    (show 0 < θ / 6 by positivity)
  refine ⟨δI, hδI, ?_⟩
  intro i h Φ U K W Δ mi mo hbuffer j C hC backward x y r hr p hq hclock hphase hsegment hin hout
  apply hgap
  exact norm_fderiv_jointElapsedPhase_ge_of_closed_shoulder hθ hC backward
    (fun a ha b hab ↦ canonicalProofLocalizer_complete_image_closed_shoulder
      hbuffer j backward ha (Or.inr hab)) x y hr p hq hclock hphase hsegment hin hout

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
