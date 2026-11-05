module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.FamilyCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.SupportedGaps

/-!
# Common nested masks, local interior gaps and conic boundary collars

This assembly constructs the masks and discharges both quantitative margin
premises with their actual producer. The low phase budget is the literal
root-flow sum at order two, on the same fixed original physical domains.
All shoulders, annular endpoints, derivative sequences, gaps and the smooth
elapsed cutoff precede the varying coefficient and requested accuracy.

The boundary gap also holds for the actual constructed supported extension;
its conic-domain restriction is derived from the closed half-buffers.
The interior conclusion here concerns the local chart phase. The stronger
`exists_uniform_conic_nested_localization_data` in `ConicLocalization` supplies
both gaps for one constructed mask family across the entire radial band of
the continued conic phase.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase

variable {d : ℕ}

/-- Construct nested physical masks together with a common local interior
squared-gradient gap and a conic boundary collar. Neither successful masks,
mask margins, gaps nor a coefficient-class compactness assumption is an input.
The exact producers are `exists_uniform_nested_physicalDirectLocalizers` for
the masks, `exists_uniform_fieldRoot_conicGeometry` for the root-flow phase
identities and budgets (including its inverse-segment clock), and the SAME
retained comparison family from
`exists_initialized_signed_no_return` for source protection.

Actual finite-chart selection supplies the displayed domain restrictions.
The local interior estimate still requires the phase point in that chart;
it does not assert this membership on the whole conic continuation.
Consumer: the normalized protected-chain estimate in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`. -/
theorem exists_uniform_nested_localization_data
    {J ι κI : Type*} [Finite J] [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
    {S : Set (Euclidean (d + 1) × Euclidean (d + 1))} (hS : IsCompact S)
    {B Ω Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {r M c C Lx κ Δ ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) (hC : 0 < C) (hLx : 0 ≤ Lx)
    (hκ : 0 < κ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hSB : ∀ p ∈ S, p.1 ∈ B) (hBball : B ⊆ ball 0 (2 * r))
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω)
    (hΩΓ : Ω ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hSV : S ⊆ V) (N : ℕ)
    (z : J → RootState (Euclidean d)) (x₀ : J → Euclidean (d + 1))
    (R₀ ρ T σ β γ Bphase aPhase bPhase : J → ℝ)
    (hγ : ∀ j, 0 < γ j) (hγβ : ∀ j, γ j ≤ β j) (hγσ : ∀ j, γ j ≤ σ j)
    (hBphase : ∀ j, 0 ≤ Bphase j) (haPhase : ∀ j, 0 < aPhase j)
    (hphysicalDomain : ∀ j, closedBall (x₀ j) (R₀ j) ⊆ closedBall 0 (2 * r)) :
    ∃ (θ a b Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < εcollar ∧ 0 < δT ∧ 0 < δI ∧ (∀ j, εcollar ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ (∀ k, 0 ≤ H k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        (∀ j, IsCompact (U j)) → (∀ j, IsCompact (K j)) → IsClosed W →
        (∀ j, U j ⊆ D j) → (∀ j, K j ⊆ D j) → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ U j ∪ K j →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B) →
        (∀ j v, v ∈ K j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (3 * ρ j) ((3 * ρ j) / 2) (T j) (Φ j)) →
        (∀ j, Δ < T j) → (∀ j, U j ⊆ closedBall (z j) ((3 * ρ j) / 2)) →
      ∀ Cphase : J → OpenPartialHomeomorph
          (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
        (∀ j, (Cphase j : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
          twoTimeProjection (Φ j)) →
        (∀ j, closedBall ((z j).1, z j) (2 * β j) ⊆ (Cphase j).target) →
        (∀ j, ContDiffOn ℝ ∞ (twoTimePhase (Cphase j)) (Cphase j).target) →
        (∀ j q, q ∈ (Cphase j).target → HasFDerivAt (twoTimePhase (Cphase j))
          (twoTimePhaseDifferential (h j) (Φ j) (Cphase j) q) q) →
        (∀ j q, q ∈ (Cphase j).target → ∀ v ∈ uIcc q.2.1 q.1,
          (twoTimeState (Φ j) (v, ((Cphase j).symm q).2)).1 = v) →
        (∀ j, cNorm (closedBall (z j) ((3 * ρ j) / 4) ×ˢ Icc (-T j / 4) (T j / 4)) 2 (Φ j) +
          (cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeState (Φ j)) +
            cNorm (closedBall ((z j).1, z j) (σ j)) 2 (twoTimeProjection (Φ j))) +
          (cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (Cphase j).symm +
            cNorm (closedBall ((z j).1, z j) (2 * β j)) 2 (twoTimePhase (Cphase j))) ≤
              Bphase j * (1 + cNorm (closedBall (x₀ j) (R₀ j)) 3 Q)) →
        (∀ j w, w ∈ ball (z j) (σ j) →
          twoTimePhase (Cphase j) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ω, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ Γ) →
        ∃ m : Fin (N + 1) → LocalizerSymbol (d + 1),
          (∀ k, IsBufferedLocalizer (m k)
            (reachableAt (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt
            (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val) ⊆
              interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆
            (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
              physicalProtectedRegion Γ) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
              closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k j, IsBufferedLocalizer
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
              (physicalDirectRelation i h Φ U K W χsource χout Δ) S k.val)
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
          (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
          (∀ k j l p, ‖iteratedFDeriv ℝ l
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ physicalDirectRelation i h Φ U K W
              (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ p q →
                closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ (k : Fin N) (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
            ∀ (x y : Euclidean (d + 1)) (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
            r' ∈ Icc 0 Δ → r' ≤ εcollar →
            p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
            spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
            spatialPart p.2.1 ∈ radialSectionBand (ℓ j) (z j).2.2 (γ j / 2)
              (aPhase j) (bPhase j) →
            (y, p.2.2.1) ∈ cthickening (θ / 2)
              (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
            (x, p.2.2.2) ∈ tsupport
              (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
            δT ≤ Localization.phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf (curriedPhase (ℓ j) (Cphase j)))
              x y (r', w)) p ∧
            ∀ Gext : TwoTimePoint (Euclidean d) → ℝ,
              (∀ q ∈ domain (ℓ j) (closedBall ((z j).1, z j) (2 * γ j)),
                Gext =ᶠ[𝓝 q] phase (ℓ j) (Cphase j)) →
              δT ≤ Localization.phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
                (SymbolBudgets.normalizedTwoTimePhase Rf
                  (fun t s v η ↦ Gext (t, (s, (v, η))))) x y (r', w)) p) ∧
          (∀ (k : Fin N) (j : J) (backward : Bool) (x y : Euclidean (d + 1))
            (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
            r' ∈ Icc 0 Δ →
            elapsedChartPoint r' p.1.1 p.2.1 ∈ (Cphase j).target →
            ((elapsedInputBase (Cphase j) r' p.1.1 p.2.1, p.2.1), r') ∈
              elapsedSegmentCarrier (coordinateSplit (i j)) (h j) (Φ j) (U j) (K j) W →
            (y, p.2.2.1) ∈ cthickening (θ / 2)
              (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
            (x, p.2.2.2) ∈ tsupport
              (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
            δI ≤ Localization.phaseGradientSquare eI
              (jointElapsedPhase backward (chartPhase (Cphase j)) x y) (r', p)) := by
  obtain ⟨θ, a, b, Rbase, H, hθ, ha, hab, hRbase, hH, hconstruct⟩ :=
    exists_uniform_nested_physicalDirectLocalizers ℓ η₀ εroot G hG hS hB hΓ
      hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
  obtain ⟨δI, hδI, hgapI⟩ := exists_uniform_interior_phaseGradientSquare_gap (J := J) hθ eI
  obtain ⟨εcollar, δT, χ, Hcollar, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hgapT⟩ := exists_uniform_finiteFamily_rootFlow_collar eT ℓ z x₀
      R₀ ρ T σ β γ Bphase aPhase bPhase hθ hM hγ hγβ hγσ hBphase haPhase (Δ := Δ)
  refine ⟨θ, a, b, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hεcollar, hδT, hδI, hεγ, hχ, hχone, hχsupp, hχcomp, hHcollar, hχjet,
    hθ, ha, hab, hRbase, hH, ?_⟩
  intro Q hQ hQM i h Φ U K D W χsource χout hU hK hWclosed hUD hKD hW
    hD hh hroot hprimitive hbase hspeed hflow htime hUflow
    Cphase hCphase htarget hphaseSmooth hphaseDifferential hsegmentClock hphaseBudget hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  obtain ⟨m, hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet,
    hactual, hcanonical, hcanonicalBounds, hcanonicalJets, hunit⟩ :=
    hconstruct Q hQ hQM i h Φ U K D W χsource χout hU hK hWclosed hUD hKD hW
      hD hh hroot hprimitive hbase hspeed z (fun j ↦ 3 * ρ j) (fun j ↦ (3 * ρ j) / 2)
      T hflow htime hUflow I g charts hgr hderiv hnorm hcover hbuffer
  have hQMlocal j : cNorm (closedBall (x₀ j) (R₀ j)) 3 Q ≤ M :=
    (cNorm_mono_set_of_contDiffAt (hphysicalDomain j) (isCompact_closedBall _ _)
      (fun _ _ ↦ hQ.contDiffAt.of_le (by simp))).trans hQM
  refine ⟨m, hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet,
    hactual, hcanonical, hcanonicalBounds, hcanonicalJets, hunit, ?_, ?_⟩
  · intro k j backward Rf hRf x y r' p hr' hrε ht hy hη hin hout
    have hgap := hgapT Q i h Φ U K W Cphase hQMlocal htarget hphaseSmooth hphaseBudget hdiag
      (m k.castSucc) (m k.succ) (hunit k) j backward Rf hRf x y r' p hr' hrε ht hy hη hin hout
    refine ⟨hgap, fun Gext hGext ↦ ?_⟩
    have hdom := elapsedChartPoint_mem_conic_boundary_buffer (ℓ j) (z j) (hγ j)
      (haPhase j) p ⟨hr'.1, hrε.trans (hεγ j)⟩ ht hy hη
    rw [(phaseGradientSquare_normalized_extension_eq eT eI (ℓ j) (Cphase j)
      hGext hRf backward x y (r', p) hdom).2]
    exact hgap
  · intro k j backward x y r' p hr' hq hsegment hin hout
    let q := elapsedChartPoint r' p.1.1 p.2.1
    have hclock := hsegmentClock j q hq q.1 right_mem_uIcc
    have hc := (twoTimeChart_inverse_coordinates (hCphase j) hq).1
    have he : (q.1, ((Cphase j).symm q).2) = (Cphase j).symm q :=
      Prod.ext hc.symm rfl
    rw [he] at hclock
    exact hgapI i h Φ U K W Δ (m k.castSucc) (m k.succ) (hunit k) j (Cphase j)
      (hCphase j) backward x y r' hr' p hq hclock
      (hphaseDifferential j q hq) hsegment hin hout

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
