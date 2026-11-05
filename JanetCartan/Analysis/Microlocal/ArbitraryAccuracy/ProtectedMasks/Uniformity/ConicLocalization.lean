module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.FamilyCollar
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension

/-!
# Coefficient-uniform localization on the complete conic carrier

The finite radial proof refinement constructs one family of physical masks.
Its unit-mask margin gives both the full conic interior gap and the full
boundary diagonal margin. The original root-flow order-two estimate then
gives one boundary collar and one smooth elapsed cutoff for those same masks.
All choices precede the current coefficient field and requested accuracy.

No operator is partitioned or changed by the radial proof cover. Both time
orientations, physical factors, whole segments, elliptic diagonals, the
original elapsed interval, and source recutting are retained. Angular
protection is imposed in physical coordinates, with canonical masks given
by `canonicalProofLocalizer`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization ConicInterior

variable {d : ℕ}

/-- Construct common nested masks, positive frequency bounds, all-order mask
and elapsed-cutoff bounds, and both gradient gaps on the complete fixed conic
radial carrier (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular:thm:no-return`). This strengthens the local-chart conclusion
of `exists_uniform_nested_localization_data` for the actual conic phase.

The root, flow, inverse-source, inverse-segment and order-two phase inputs
are the literal outputs of `exists_uniform_fieldRoot_conicGeometry`, with
`R = 3ρ`, `rFlow = 3ρ/2`. Its `fieldDomain` is radially invariant;
`fieldRoot_maskAssembly_primitives` and
`fieldRoot_maskAssembly_radial_invariance` extract the displayed root inputs.
The common C³ bound is restricted to each original physical domain below.
The comparison charts and source cover are the SAME retained family from
`exists_initialized_signed_no_return_with_graph_bounds`.

Actual finite chart selection supplies their displayed fixed domain buffers
and original elapsed interval. The full carrier uses `r' ∈ Icc 0 Δ` and the
constructor's supported phase domain `r' ≤ γ j`; the proof does not replace
`Δ` by a smaller interval. Every mask, radial buffer, margin, gradient gap
and collar is constructed here, without coefficient-class compactness.
The supported extension is constructed from the same compact phase buffer
by `exists_continuous_conicPhase_extension`; no extension germ is assumed.
The final four conclusions are the exact interior and boundary nonvanishing
inputs to `GradientGaps` and `UniformCollar`, for both the original conic
phase and its constructed extension. The boundary derivative is evaluated
at elapsed time zero for EVERY point of the full carrier, not just those
points already in the collar. All exclusions retain the complete closed
input shoulder and complementary output support.
Consumer: `finiteChain_observation_rapidDecayAt`. -/
theorem exists_uniform_conic_nested_localization_data
    {J ι κI : Type*} [Finite J] [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables (Euclidean (d + 1)))) (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (z : J → RootState (Euclidean d)) (εroot G : J → ℝ) (hG : ∀ j, 0 ≤ G j)
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
    (x₀ : J → Euclidean (d + 1)) (R₀ ρ T σ β γ Bphase aPhase bPhase : J → ℝ)
    (hρ : ∀ j, 0 < ρ j) (hσ : ∀ j, 0 < σ j)
    (hσρ : ∀ j, 2 * σ j ≤ (3 * ρ j) / 4)
    (hγ : ∀ j, 0 < γ j) (hγβ : ∀ j, γ j ≤ β j) (hγσ : ∀ j, γ j ≤ σ j)
    (hBphase : ∀ j, 0 ≤ Bphase j) (haPhase : ∀ j, 0 < aPhase j)
    (hphysicalDomain : ∀ j, closedBall (x₀ j) (R₀ j) ⊆ closedBall 0 (2 * r)) :
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ a b Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ γ j) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2 * r)) 3 Q ≤ M →
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ),
        IsClosed W → W ⊆ closedBall 0 (2 * r) →
        (∀ j, IsOpen (D j)) → (∀ j, ContDiffOn ℝ ∞ (h j) (D j)) →
        (∀ j, closedBall (z j) (3 * ρ j) ⊆ D j) →
        (∀ j w, w ∈ D j → ∀ s : ℝ, 0 < s →
          (w.1, (w.2.1, s • w.2.2)) ∈ D j ∧ h j (w.1, (w.2.1, s • w.2.2)) = s * h j w) →
        (∀ j v, v ∈ D j → v.2.2 ≠ 0 ∧
          determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
            ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0 ∧
          fderiv ℝ (determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1))))
            ((coordinateSplit (i j)).symm (h j v, v.2.2))
            ((coordinateSplit (i j)).symm (1, 0)) ≠ 0) →
        (∀ j v, v ∈ closedBall (z j) (3 * ρ j) →
          v.2.2 ∈ closedBall (z j).2.2 (εroot j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        (∀ j v, v ∈ closedBall (z j) (3 * ρ j) →
          (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B ∩ W) →
        (∀ j v, v ∈ D j → κ ≤ |pencilRootSpeed Q (coordinateSplit (i j)) (h j) v|) →
        (∀ j, ODE.IsSmoothFlowOn (rootHamiltonField (h j))
          (z j) (3 * ρ j) ((3 * ρ j) / 2) (T j) (Φ j)) → (∀ j, Δ < T j) →
      ∀ Cphase : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)),
        (∀ j, (Cphase j : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
          twoTimeProjection (Φ j)) →
        (∀ j, (Cphase j).source = ball ((z j).1, z j) (σ j)) →
        (∀ j, closedBall ((z j).1, z j) (2 * β j) ⊆ (Cphase j).target) →
        (∀ j, ContDiffOn ℝ ∞ (twoTimePhase (Cphase j)) (Cphase j).target) →
        (∀ j q, q ∈ (Cphase j).target → HasFDerivAt (twoTimePhase (Cphase j))
          (twoTimePhaseDifferential (h j) (Φ j) (Cphase j) q) q) →
        (∀ j q, q ∈ (Cphase j).target → ∀ t ∈ uIcc q.2.1 q.1,
          twoTimeState (Φ j) (t, ((Cphase j).symm q).2) ∈ closedBall (z j) (3 * ρ j) ∧
            (twoTimeState (Φ j) (t, ((Cphase j).symm q).2)).1 = t) →
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
        let irad := fun k : (j : J) × Fin (n j) ↦ i k.1
        let hrad := fun k : (j : J) × Fin (n j) ↦ h k.1
        let Φrad := fun k : (j : J) × Fin (n j) ↦
          radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
        let Ur := fun k : (j : J) × Fin (n j) ↦ Urad k.1 k.2
        let Kr := fun k : (j : J) × Fin (n j) ↦
          rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' '' closedBall (z k.1) (3 * ρ k.1)
        let Ractual := physicalDirectRelation irad hrad Φrad Ur Kr W
          (fun k ↦ χsource k.1) (fun k ↦ χout k.1) Δ
        let Runit := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
        ∃ (Gext : J → TwoTimePoint (Euclidean d) → ℝ)
          (m : Fin (N + 1) → LocalizerSymbol (d + 1)),
          (∀ j, Continuous (Gext j) ∧ ContDiffOn ℝ ∞ (Gext j) {q | q.2.2.2 ≠ 0} ∧
            (∀ (q : TwoTimePoint (Euclidean d)) (s : ℝ), 0 < s →
              Gext j (q.1, (q.2.1, (q.2.2.1, s • q.2.2.2))) = s * Gext j q) ∧
            ∀ q ∈ ConicPhase.domain (ℓ j) (closedBall ((z j).1, z j) (2 * γ j)),
              Gext j =ᶠ[𝓝 q] ConicPhase.phase (ℓ j) (Cphase j)) ∧
          (∀ k, IsBufferedLocalizer (m k)
            (reachableAt Ractual S k.val)
            (physicalProtectedRegion Γ)) ∧
          IsBufferedLocalizer (m 0) S V ∧
          cthickening θ (tsupport (m 0)) ⊆ V ∧
          (∀ k, cthickening θ (reachableAt
            Ractual S k.val) ⊆
              interior {p | m k p = 1}) ∧
          (∀ k, cthickening θ (tsupport (m k)) ⊆
            (closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∩
              physicalProtectedRegion Γ) ∧
          (∀ k l p, ‖iteratedFDeriv ℝ l (m k) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ Ractual p q →
              closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ k j, IsBufferedLocalizer
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k))
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' reachableAt
              Ractual S k.val)
            (adaptedPhaseEquiv (coordinateSplit (i j)) ⁻¹' physicalProtectedRegion Γ)) ∧
          (∀ k j, tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) ⊆
            closedBall 0 Rbase ×ˢ PhysicalShells.frequencyAnnulus a b) ∧
          (∀ k j l p, ‖iteratedFDeriv ℝ l
            (canonicalProofLocalizer (coordinateSplit (i j)) (m k)) p‖ ≤ H l) ∧
          (∀ k : Fin N, ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
            p = q ∨ Runit p q →
                closedBall q θ ⊆ interior {p | m k.succ p = 1}) ∧
          (∀ (k : Fin N) (χ₂ χ₃ : Euclidean (d + 1) → ℝ),
            EqOn χ₃ 1 (tsupport χ₂) →
            ∀ p ∈ cthickening θ (tsupport (m k.castSucc)), ∀ q,
              sourceRecutRelation χ₂ Ractual p q →
                χ₃ p.1 = 1 ∧ closedBall q θ ⊆ interior {q | m k.succ q = 1}) ∧
          ∀ (k : Fin N) (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
          ∀ (x y : Euclidean (d + 1)) (r' : ℝ) (p : JointVariables (Euclidean (d + 1))),
            r' ∈ Icc 0 Δ → r' ≤ γ j →
            p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
            spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
            spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2
              (γ j / 2) (aPhase j) (bPhase j) →
            (y, p.2.2.1) ∈ cthickening (θ / 2)
              (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) (m k.castSucc))) →
            (x, p.2.2.2) ∈ tsupport
              (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) (m k.succ) q) →
            (δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ∧
              (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
                (SymbolBudgets.normalizedTwoTimePhase Rf
                  (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (r', w)) p)) ∧
            δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
                (SymbolBudgets.normalizedTwoTimePhase Rf
                  (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ∧
              (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
                (SymbolBudgets.normalizedTwoTimePhase Rf
                  (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (r', w)) p) ∧
            fderiv ℝ (jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf
                (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y) (r', p) ≠ 0 ∧
            fderiv ℝ (fun w ↦ jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf
                (ConicPhase.curriedPhase (ℓ j) (Cphase j))) x y (0, w)) p ≠ 0 ∧
            fderiv ℝ (jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf
                (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y) (r', p) ≠ 0 ∧
            fderiv ℝ (fun w ↦ jointElapsedPhase backward
              (SymbolBudgets.normalizedTwoTimePhase Rf
                (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (0, w)) p ≠ 0 := by
  have hnest j := constructor_source_radius_nesting (hρ j) (hσρ j)
  obtain ⟨n, cRad, hcRad, Urad, θ, a, b, Rbase, δI, H,
    hθ, ha, hab, hRbase, hδI, hH, hconstruct⟩ :=
    exists_uniform_radial_nested_localizers_and_gap eI ℓ z εroot G hG
      hS hB hΓ hr hM hc hC hLx hκ hΔ hε hSB hBball hsource hΩΓ hV hSV N
      (fun j ↦ 3 * ρ j) (fun j ↦ (3 * ρ j) / 2) T σ γ aPhase bPhase
      hγ haPhase (fun j ↦ (hσ j).le) (fun j ↦ (hnest j).1) (fun j ↦ (hnest j).2)
  obtain ⟨εcollar, δT, χ, Hcollar, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hgapT⟩ := exists_uniform_finiteFamily_rootFlow_collar_of_diagonal
      eT ℓ z x₀ R₀ ρ T σ β γ Bphase aPhase bPhase
      hθ hM hγ hγβ hγσ hBphase haPhase (Δ := Δ)
  refine ⟨n, cRad, hcRad, Urad, θ, a, b, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro Q hQ hQM i h Φ D W χsource χout hWclosed hW hD hh hRD hhom hroot
    hprimitive hbase hspeed hflow htime Cphase hCphase hCsource htarget hsmooth
    hdiff hsegments hbudget hdiag I g charts hgr hderiv hnorm hcover hbuffer
  have htargetγ j : closedBall ((z j).1, z j) (2 * γ j) ⊆ (Cphase j).target :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (hγβ j) (by norm_num))).trans
      (htarget j)
  obtain ⟨m, hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet,
    hactual, hcanonical, hcanonicalBounds, hcanonicalJets, hunit, hgapI⟩ :=
    hconstruct Q hQ hQM i h Φ D W χsource χout hWclosed hW hD hh hRD hhom hroot
      hprimitive hbase hspeed hflow htime Cphase hCphase hCsource htargetγ
      hdiff hsegments I g charts hgr hderiv hnorm hcover hbuffer
  choose Gext hGcont hGsmooth hGhom hGerm using fun j ↦
    ConicPhase.exists_continuous_conicPhase_extension (ℓ j) (Cphase j)
      (isCompact_closedBall _ _) (htargetγ j) (hsmooth j)
  have hQMlocal j : cNorm (closedBall (x₀ j) (R₀ j)) 3 Q ≤ M :=
    (cNorm_mono_set_of_contDiffAt (hphysicalDomain j) (isCompact_closedBall _ _)
      (fun _ _ ↦ hQ.contDiffAt.of_le (by simp))).trans hQM
  refine ⟨Gext, m, fun j ↦ ⟨hGcont j, hGsmooth j, hGhom j, hGerm j⟩,
    hm, hfirst, hsourceShoulder, hreachable, hshoulder, hjet,
    hactual, hcanonical, hcanonicalBounds, hcanonicalJets, hunit, ?_, ?_⟩
  · intro k χ₂ χ₃ hcut p hp q hpq
    exact sourceRecutRelation_mem_closed_shoulder_plateau (hactual k) hcut hp hpq
  · intro k j backward Rf hRf x y r' p hr' hrγ ht hy hη hin hout
    obtain ⟨hinterior, hextension⟩ := hgapI k j backward Rf hRf x y r' p
      hr' hrγ ht hy hη hin hout
    have hboundary r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :=
      hgapT Q i Φ Cphase hQMlocal htarget hsmooth hbudget hdiag
        (m k.castSucc) (m k.succ) (fun q hq ↦ hunit k q hq q (Or.inl rfl))
        j backward Rf hRf x y r₁ p hr₁ hrε ht hy hη hin hout
    have hboundaryExt r₁ (hr₁ : r₁ ∈ Icc 0 Δ) (hrε : r₁ ≤ εcollar) :
        δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase backward
          (SymbolBudgets.normalizedTwoTimePhase Rf
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (r₁, w)) p := by
      have hdom := elapsedChartPoint_mem_conic_boundary_buffer (ℓ j) (z j) (hγ j)
        (haPhase j) p ⟨hr₁.1, hrε.trans (hεγ j)⟩ ht hy hη
      rw [(phaseGradientSquare_normalized_extension_eq eT eI (ℓ j) (Cphase j)
        (hGerm j) hRf backward x y (r₁, p) hdom).2]
      exact hboundary r₁ hr₁ hrε
    have hext := hextension (Gext j) (hGerm j)
    refine ⟨⟨hinterior, hboundary r' hr'⟩, hext, hboundaryExt r' hr', ?_, ?_, ?_, ?_⟩
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδI.trans_le hinterior)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hboundary 0 ⟨le_rfl, hΔ⟩ hεcollar.le))
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδI.trans_le hext)
    · exact (FiniteChain.Retarded.phaseGradientSquare_basis_pos_iff _ _ _).mp
        (hδT.trans_le (hboundaryExt 0 ⟨le_rfl, hΔ⟩ hεcollar.le))

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
