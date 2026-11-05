module

public import JanetCartan.Analysis.Microlocal.SelectedSectorProtection.SelectedGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# Nested proof masks on the selected sector witnesses

Relative application of the coefficient-uniform protected-mask construction to
one finite direct-operator selection. The original roots, flows, inverse charts,
source and endpoint masks are parameters throughout; none is selected again.
The comparison charts are the retained outputs of initialized no-return for
that very coefficient field. Sources: `app:ch_regular:thm:no-return`,
`app:ch_regular:lem:finite-chain`, and `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.UniformAmplitudes
open RegularSector.FiniteAssembly RegularSector.FiniteEvolution RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral
open ProtectedMasks ProtectedMasks.ConicInterior ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- Apply the complete conic mask conclusion to the ALREADY selected finite
operator witnesses (`app:ch_regular:lem:finite-chain`). The local certificates
are returned by `exists_finite_direct_operator_bounds_with_protection_certificates`;
the phase identities below are retained by that same endpoint. The initialized
comparison charts, their gradient bounds, source cover and angular buffer are
exactly the outputs of `exists_initialized_signed_no_return_with_graph_bounds`,
with the identical globally extended `Q`. The fixed response cutoffs supply the
source product and its prescribed open buffer.

The global C³ bound is supplied by the initialized frame extension. All mask
constants precede `Q`; only the proof masks and losses depend on depth. The
original endpoint, input mask, flow, inverse and physical domain are unchanged.
The common elapsed bound contains the whole physical support product by
`selected_physical_support_elapsed_bound`. The conclusion includes physical
and canonical masks, both signed relations, elliptic diagonals, source recuts,
all-order grades, interior gaps and zero-elapsed boundary exclusions.

This is the relative finite-family application. Choosing the finite family
inside the initialized physical domain and inserting the same-reference
comparison certificates remains explicit at its call site. It asserts no
unconditional response or leakage estimate. -/
theorem exists_selectedSector_nested_proof_masks_of_coefficient_bound
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hΩ : IsOpen Ω)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {r Mglobal c C Lx ε : ℝ}
    (hr : 0 < r) (hMglobal : 0 ≤ Mglobal) (hcgraph : 0 < c) (hCgraph : 0 < C)
    (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hphysical : closedBall x RQ ⊆ ball 0 (2*r))
    (hΩΓ : Ωsource ⊆ interior Γ)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball x f.physicalRadius)
    (hχ₂source : tsupport χ₂ ⊆ ball 0 r)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ interior Ωsource)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (output : E → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ) (haPhase : ∀ p, 0 < aPhase p) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let ρ := fun p : J ↦ (f.chart p).rootRadius / 3
    let γ := fun p : J ↦ (f.chart p).maskRadius
    let W := closedBall x RQ
    let S := tsupport χ₂ ×ˢ Ksource
    let Δ := 6 * f.physicalRadius
    EqOn f.inputMask 1 (tsupport χ₂) ∧
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
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q), cNorm (closedBall 0 (2*r)) 3 Q ≤ Mglobal →
      let h := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) Ω (ℓ p)
        (z p).2.2 (εroot p)
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP),
        (∀ p, SelectedProtectionData (f.chart p) (T p) (speed p) (G p) (rootCost p)
          Q (Φ p) (Cphase p)) →
        (∀ p, ContDiffOn ℝ ∞ (h p) (D p)) →
        (∀ p w, w ∈ D p → ∀ t : ℝ, 0 < t →
          h p (w.1, (w.2.1, t • w.2.2)) = t * h p w) →
        (∀ p, (Cphase p : TP → TP) = twoTimeProjection (Φ p)) →
        (∀ p, (Cphase p).source = ball ((z p).1, z p) (f.chart p).sourceRadius) →
        (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cphase p).target) →
        (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cphase p)) (Cphase p).target) →
        (∀ p q, q ∈ (Cphase p).target → HasFDerivAt (twoTimePhase (Cphase p))
          (twoTimePhaseDifferential (h p) (Φ p) (Cphase p) q) q) →
        (∀ p w, w ∈ ball (z p) (f.chart p).sourceRadius →
          twoTimePhase (Cphase p) (w.1, w) = inner ℝ w.2.1 w.2.2) →
      ∀ (I : Type*) (g : I → ComparisonGeometry (Euclidean (d + 1)))
        (charts : (j : I) → ComparisonChart
          (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g j)),
        (∀ j, r ≤ (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
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
          (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
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
  intro J i ℓ z εroot ρ γ W S Δ
  refine ⟨selected_source_recut_plateau f χ₂ hχ₂support, ?_⟩
  obtain ⟨κ, hκ, hκspeed⟩ := exists_selected_common_root_speed f T speed G rootCost hc
  have hρ p : 0 < ρ p := div_pos (f.chart p).rootRadius_pos (by norm_num)
  have hρeq p : 3 * ρ p = (f.chart p).rootRadius := by dsimp [ρ]; ring
  have hβeq p : 2 * ((f.chart p).targetRadius / 2) = (f.chart p).targetRadius := by ring
  have hσρ p : 2 * (f.chart p).sourceRadius ≤ (3 * ρ p) / 4 := by
    rw [hρeq]; exact (hc p).2.2.2.2.1
  have hSB : ∀ q ∈ S, q.1 ∈ W := by
    intro q hq
    apply f.physicalBall_coefficientDomain
    apply ball_subset_closedBall
    exact (ball_subset_ball (by linarith [f.physicalRadius_pos])) (hχ₂support hq.1)
  have hsource : ∀ q ∈ S, q.1 ∈ ball 0 r ∧ q.2 ≠ 0 ∧
      normalizedCovector q.2 ∈ interior Ωsource :=
    fun q hq ↦ ⟨hχ₂source hq.1, hsourceFrequency q.2 hq.2⟩
  obtain ⟨n, cRad, hcRad, Urad, θ, a, b, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hconstruct⟩ :=
    exists_uniform_conic_nested_localization_data eT eI ℓ z εroot G
      (fun p ↦ (hc p).2.2.1.le) (hχ₂.isCompact.prod hKsource) (isCompact_closedBall x RQ)
      hΓ.isClosed hr hMglobal hcgraph hCgraph hLx hκ
      (show 0 ≤ Δ by dsimp [Δ]; exact mul_nonneg (by norm_num) f.physicalRadius_pos.le) hε hSB hphysical hsource hΩΓ hV hSV N
      (fun _ ↦ x) (fun _ ↦ RQ) ρ T (fun p ↦ (f.chart p).sourceRadius)
      (fun p ↦ (f.chart p).targetRadius / 2) γ (fun p ↦ (f.chart p).phaseCost 2)
      aPhase bPhase hρ (fun p ↦ (f.chart p).sourceRadius_pos) hσρ
      (fun p ↦ (f.chart p).maskRadius_pos)
      (fun p ↦ (selected_mask_radius_protection_bounds f hradii p).2.1)
      (fun p ↦ (f.chart p).maskRadius_lt_sourceRadius.le)
      (fun p ↦ ((f.chart p).phaseCost_pos 2).le) haPhase
      (fun _ ↦ hphysical.trans ball_subset_closedBall)
  refine ⟨n, cRad, hcRad, Urad, θ, a, b, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro Q hQ hQlow h D Φ Cphase hd hh hhom hCphase hCsource htarget hsmooth hdiff hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  have hroot p := selected_root_mask_primitives f p (hc p) Q (Φ p) (Cphase p) (hd p)
  have hrootBall p : closedBall (z p) (3 * ρ p) ⊆ D p := by
    rw [hρeq]; exact (hroot p).1
  have hprimitive p : ∀ v ∈ closedBall (z p) (3 * ρ p),
      v.2.2 ∈ closedBall (z p).2.2 (εroot p) ∧
      (1/2 : ℝ) ≤ ℓ p v.2.2 ∧ |h p v| ≤ ℓ p v.2.2 * G p := by
    rw [hρeq]; exact (hroot p).2.2.1
  have hbase p : ∀ v ∈ closedBall (z p) (3 * ρ p),
      (coordinateSplit (i p)).symm (v.1, v.2.1) ∈ W ∩ W := by
    rw [hρeq]
    exact fun v hv ↦ ⟨(hroot p).2.2.2.1 v hv, (hroot p).2.2.2.1 v hv⟩
  have hflow p : ODE.IsSmoothFlowOn (rootHamiltonField (h p))
      (z p) (3 * ρ p) ((3 * ρ p) / 2) (T p) (Φ p) := by
    rw [hρeq]; exact (hd p).2.1
  have hsegments p : ∀ q ∈ (Cphase p).target, ∀ u ∈ uIcc q.2.1 q.1,
      twoTimeState (Φ p) (u, ((Cphase p).symm q).2) ∈ closedBall (z p) (3 * ρ p) ∧
      (twoTimeState (Φ p) (u, ((Cphase p).symm q).2)).1 = u := by
    rw [hρeq]
    exact selected_inverse_complete_segments f p Q (Φ p) (Cphase p) (hd p)
  apply hconstruct Q hQ hQlow i h Φ D W (chartInputMask f)
    (fun p ↦ endpointOutputMask f p output) isClosed_closedBall
    (hphysical.trans ball_subset_closedBall)
    (fun p ↦ isOpen_fieldDomain _ hΩ _ _ _) hh hrootBall
    (fun p ↦ fieldRoot_maskAssembly_radial_invariance _ _ _ _ _ Q _ (hhom p))
    (fun p ↦ (hroot p).2.1) hprimitive hbase
    (fun p v hv ↦ (hκspeed p).trans ((hroot p).2.2.2.2 v hv)) hflow
    (fun p ↦ (selected_common_elapsed_lt_evolutionTime f p (hc p)).2.2)
    Cphase hCphase hCsource
    (fun p ↦ by rw [hβeq]; exact htarget p) hsmooth hdiff hsegments
    (fun p ↦ by
      rw [hρeq, hβeq]
      exact (hd p).2.2.2.2.2.2.2.2.2.2.2.2.1 2)
    hdiag I g charts hgr hderiv hnorm hcover hbuffer

end JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
