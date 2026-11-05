module

public import JanetCartan.Analysis.Microlocal.SelectedSectorProtection.Application
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.InitializedProtection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.GraphTransport.CoefficientBudget

/-!
# Application on the same initialized signed-source geometry

The finite family is the one already selected on the initialized physical
ball. The reference, current-map lift and coefficient extension below are
retained by `exists_initialized_signed_no_return_with_graph_bounds`. The
C³ bound is constructed from that lift's original componentwise C⁶ bound.
No second reference, flow, coefficient field or finite cover is selected.
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
open RegularSector.FiniteAssembly RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral
open ProtectedMasks ProtectedMasks.ConicInterior ActualCarriers HamiltonPhase ProtectedFlow PhaseCover
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
variable {d : ℕ} {r M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TP" => TwoTimePoint (Euclidean d)

/-- The retained current-map lift supplies smoothness of its literal extended
pencil. This is the globally smooth symbol used by the SAME comparison charts
and selected roots (`app:ch_regular:thm:no-return`). -/
theorem selected_initialized_extendedPencil_contDiff
    {b B δ : ℝ} (hbB : b < B) (extension : BallExtension.Parameters E)
    (hp0 : extension.center = 0) (hpb : extension.radius ≤ b)
    (F : ProjectedImmersionNeighborhood (embeddingDimension (d+1))
      (ball 0 B) (closedBall 0 b) δ) :
    ContDiff ℝ ∞ (extendedProjectedStress extension F.1) := by
  exact contDiff_affineFrameExtension extension ((frameOfImmersion isOpen_ball F).2.1.mono
    (by rw [hp0]; exact closedBall_subset_ball (hpb.trans_lt hbB)))

/-- The complete output of the selected protected-mask construction, with
physical and canonical masks, whole signed relations, frequency bounds,
all-order grades, source recuts and both phase-gradient exclusions. This is
only an output proposition; `exists_selectedSector_nested_proof_masks` proves
it from the retained primitive producers (`app:ch_regular:lem:finite-chain`). -/
def SelectedSectorNestedMaskConclusion
    {Ω : Set E} {x : E} {RQ : ℝ}
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    (χ₂ : E → ℝ) (Ksource : Set E) (V : Set (E × E)) (Γ : Set E)
    (output : E → ℝ) (N : ℕ) (aPhase bPhase : f.centers → ℝ)
    (n : f.centers → ℕ) (cRad : (j : f.centers) → Fin (n j) → ℝ)
    (hcRad : ∀ j k, 0 < cRad j k)
    (Urad : (j : f.centers) → Fin (n j) → Set Z)
    (θ a b Rbase εcollar δT δI : ℝ) (H : ℕ → ℝ)
    (Q : E → Fin (d+1) → MetricTensor (d+1))
    (Φ : f.centers → Z × ℝ → Z) (Cphase : f.centers → OpenPartialHomeomorph TP TP) : Prop :=
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) x).1,
      ((coordinateSplit (i p) x).2, (coordinateSplit (i p) p.val.val).2))
    let W := closedBall x RQ
    let S := tsupport χ₂ ×ˢ Ksource
    let Δ := 6 * f.physicalRadius
    let h : J → Z → ℝ := fun p ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
    let irad : ((j : J) × Fin (n j)) → Fin (d+1) := fun k ↦ i k.1
    let hrad : ((j : J) × Fin (n j)) → Z → ℝ := fun k ↦ h k.1
    let Φrad : ((j : J) × Fin (n j)) → Z × ℝ → Z := fun k ↦
      radialFlow (cRad k.1 k.2) (hcRad k.1 k.2).ne' (Φ k.1)
    let Ur : ((j : J) × Fin (n j)) → Set Z := fun k ↦ Urad k.1 k.2
    let Kr : ((j : J) × Fin (n j)) → Set Z := fun k ↦
      rootRadialEquiv (cRad k.1 k.2) (hcRad k.1 k.2).ne' ''
        closedBall (z k.1) (f.chart k.1).rootRadius
    let Ractual : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W
      (fun k ↦ chartInputMask f k.1) (fun k ↦ endpointOutputMask f k.1 output) Δ
    let Runit : (E × E) → (E × E) → Prop := physicalDirectRelation irad hrad Φrad Ur Kr W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ
    ∃ (Gext : J → TwoTimePoint (Euclidean d) → ℝ)
      (m : Fin (N + 1) → LocalizerSymbol (d + 1)),
      (∀ j, Continuous (Gext j) ∧ ContDiffOn ℝ ∞ (Gext j) {q | q.2.2.2 ≠ 0} ∧
        (∀ (q : TwoTimePoint (Euclidean d)) (s : ℝ), 0 < s →
          Gext j (q.1, (q.2.1, (q.2.2.1, s • q.2.2.2))) = s * Gext j q) ∧
        ∀ q ∈ ConicPhase.domain (ℓ j) (closedBall ((z j).1, z j) (2 * (f.chart j).maskRadius)),
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
        r' ∈ Icc 0 Δ → r' ≤ (f.chart j).maskRadius →
        p.1.1 0 ∈ closedBall (z j).1 ((f.chart j).maskRadius / 2) →
        spatialPart p.1.1 ∈ closedBall (z j).2.1 ((f.chart j).maskRadius / 2) →
        spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2
          ((f.chart j).maskRadius / 2) (aPhase j) (bPhase j) →
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
            (fun t s v η ↦ Gext j (t, (s, (v, η))))) x y (0, w)) p ≠ 0

/-- Construct the entire nested-mask conclusion on the same initialized
signed-source product and the already selected finite direct operators
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`).

Apply `exists_finite_direct_operator_bounds_with_protection_certificates` on
`closedBall 0 r` inside the global extended-coefficient domain; retain its
`f,T,speed,G,rootCost` and, after each current map, its `Φ,Cphase` and displayed
primitive certificates. The reference `Gref`, the SAME-map `lift`, extension,
angular nesting, comparison charts, gradient bounds, source cover and buffered
graph image below are the literal retained outputs of
`exists_initialized_signed_no_return_with_graph_bounds`. The source frequency
set is the original compact rescaled cutoff support, whose normalized directions
lie in the retained inner signed-source neighborhood `Ω₀`.

Every extra geometric input of the generic mask theorem is discharged:
the C³ bound comes from `exists_uniform_extendedProjectedStress_cNorm_three_bound`,
the physical and source domains from the original finite masks, root speed
and complete inverse segments from the selected certificates, and comparison
coverage and angular inclusion from the same initialized charts. Constants
precede the current map, and both signs use the same flow. The equality in the
conclusion identifies the pencil literally with the extension of that current
map, using the initializer's map-preserving lift.

This relative application selects no operators and no replacement initializer.
The parent retains the same-inverse response cutoff/source instantiation and
the leakage and finite-chain estimates. -/
theorem exists_selectedSector_nested_proof_masks
    (f : ActualMaskFamily univ (0 : E) r A₀ K M)
    (T speed G : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hc : ∀ p, LocalProtectionCertificate (f.chart p) (T p) (speed p) (G p) (rootCost p))
    (hradii : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (Gref : FlatReference (d+1)) {b B δ dmap : ℝ} (hbB : b < B) (hδ : 0 < δ)
    (extension : BallExtension.Parameters E) (hp0 : extension.center = 0)
    (hpb : extension.radius ≤ b) (m₀ : ℕ)
    (lift : PrimitiveMapNeighborhood Gref B (m₀+2) dmap →
      ProjectedImmersionNeighborhood (embeddingDimension (d+1)) (ball 0 B) (closedBall 0 b) δ)
    (hsame : ∀ F, (lift F).1 = F.1)
    {ι κI : Type*} [Fintype ι] [Fintype κI]
    (eT : Module.Basis ι ℝ (JointVariables E))
    (eI : Module.Basis κI ℝ (ℝ × JointVariables E))
    {Ω₀ Ωsource Γ : Set E} (hΓ : IsCompact Γ)
    {c C Lx ε : ℝ}
    (hr : 0 < r) (hcgraph : 0 < c) (hCgraph : 0 < C) (hLx : 0 ≤ Lx) (hε : 0 < ε)
    (hΩ₀ : Ω₀ ⊆ interior Ωsource) (hΩΓ : Ωsource ⊆ interior Γ)
    (χ₂ : E → ℝ) (hχ₂ : HasCompactSupport χ₂)
    (hχ₂support : tsupport χ₂ ⊆ ball 0 f.physicalRadius)
    {Ksource : Set E} (hKsource : IsCompact Ksource)
    (hsourceFrequency : ∀ ξ ∈ Ksource, ξ ≠ 0 ∧ normalizedCovector ξ ∈ Ω₀)
    {V : Set (E × E)} (hV : IsOpen V) (hSV : tsupport χ₂ ×ˢ Ksource ⊆ V)
    (output : E → ℝ) (N : ℕ)
    (aPhase bPhase : f.centers → ℝ) (haPhase : ∀ p, 0 < aPhase p) :
    let J := f.centers
    let i := fun p : J ↦ (f.chart p).index
    let ℓ := fun p : J ↦ (f.chart p).radialSection
    let z : J → Z := fun p : J ↦ ((coordinateSplit (i p) (0 : E)).1,
      ((coordinateSplit (i p) (0 : E)).2, (coordinateSplit (i p) p.val.val).2))
    let εroot := fun p : J ↦ (f.chart p).coefficientRadius
    let QF := fun F : PrimitiveMapNeighborhood Gref B (m₀+2) dmap ↦
      extendedProjectedStress extension (lift F).1
    let hQF : ∀ F, ContDiff ℝ ∞ (QF F) := fun F ↦
      selected_initialized_extendedPencil_contDiff hbB extension hp0 hpb (lift F)
    EqOn f.inputMask 1 (tsupport χ₂) ∧
    ∃ (n : J → ℕ) (cRad : (j : J) → Fin (n j) → ℝ)
      (hcRad : ∀ j k, 0 < cRad j k)
      (Urad : (j : J) → Fin (n j) → Set (RootState (Euclidean d))),
    ∃ (θ a b Rbase εcollar δT δI : ℝ) (H Hcollar : ℕ → ℝ)
      (χ : ℝ × JointVariables (Euclidean (d + 1)) → ℂ),
      0 < θ ∧ 0 < a ∧ a < b ∧ 0 < Rbase ∧ 0 < δI ∧ (∀ k, 0 ≤ H k) ∧
      0 < εcollar ∧ 0 < δT ∧ (∀ j, εcollar ≤ (f.chart j).maskRadius) ∧ ContDiff ℝ ∞ χ ∧
      (∀ p, |p.1| ≤ εcollar / 4 → χ p = 1) ∧
      tsupport χ ⊆ {p | |p.1| ≤ εcollar / 2} ∧
      tsupport (1 - χ) ⊆ {p | εcollar / 4 ≤ |p.1|} ∧
      (∀ k, 0 ≤ Hcollar k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k χ p‖ ≤ Hcollar k) ∧
      ∀ F : PrimitiveMapNeighborhood Gref B (m₀ + 2) dmap,
      let Q : E → Fin (d+1) → MetricTensor (d+1) := QF F
      let hQ : ContDiff ℝ ∞ Q := hQF F
      let h : J → Z → ℝ := fun p : f.centers ↦ fieldRoot (coordinateSplit (i p)) Q (f.chart p).root
      let D : J → Set Z := fun p : f.centers ↦ fieldDomain (coordinateSplit (i p)) univ (ℓ p)
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
        (∀ j, 3*r < (g j).radius) →
        (∀ j η, η ∈ (g j).parameters → ∀ x ∈ closedBall 0 (2 * r),
          ‖fderiv ℝ ((charts j).gradientMap η) x‖ ≤ Lx) →
        (∀ η : ComparisonGeometry.ParameterFamily g, ∀ x ∈ closedBall 0 (2 * r),
          c ≤ ‖ComparisonChart.familyGradient charts η x‖ ∧
            ‖ComparisonChart.familyGradient charts η x‖ ≤ C) →
        (∀ p ∈ closedBall 0 r ×ˢ Ωsource, normalizedSymbol Q p = 0 →
          p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ) →
        (∀ p ∈ positiveConicLift (ComparisonChart.familyGradient charts) (ball 0 (2 * r)) univ,
          closedBall (normalizedCovector p.2) ε ⊆ interior Γ \ cubeBadSubspaceUnion (d+1)) →
        Q = extendedProjectedStress extension F.1 ∧
        SelectedSectorNestedMaskConclusion f eT eI χ₂ Ksource V Γ output N aPhase bPhase
          n cRad hcRad Urad θ a b Rbase εcollar δT δI H Q Φ Cphase := by
  intro J i ℓ z εroot QF hQF
  obtain ⟨Mglobal, hMglobal, hbudget⟩ :=
    exists_uniform_extendedProjectedStress_cNorm_three_bound
      (N := embeddingDimension (d+1)) isOpen_ball (isCompact_closedBall (0 : E) b)
      (closedBall_subset_ball hbB) extension
      (by rw [hp0]; exact closedBall_subset_closedBall hpb) hδ (2*r)
  obtain ⟨hrecut, n, cRad, hcRad, Urad, θ, a, bfreq, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, hconstruct⟩ :=
    exists_selectedSector_nested_proof_masks_of_coefficient_bound f isOpen_univ
      T speed G rootCost hc hradii eT eI hΓ hr hMglobal hcgraph hCgraph hLx hε
      (closedBall_subset_ball (by linarith)) hΩΓ χ₂ hχ₂ hχ₂support
      (hχ₂support.trans (selected_physical_core_subset_coefficient_ball f))
      hKsource (fun ξ hξ ↦ ⟨(hsourceFrequency ξ hξ).1, hΩ₀ (hsourceFrequency ξ hξ).2⟩)
      hV hSV output N aPhase bPhase haPhase
  refine ⟨hrecut, n, cRad, hcRad, Urad, θ, a, bfreq, Rbase, εcollar, δT, δI, H, Hcollar, χ,
    hθ, ha, hab, hRbase, hδI, hH, hεcollar, hδT, hεγ, hχ, hχone, hχsupp, hχcomp,
    hHcollar, hχjet, ?_⟩
  intro F Q hQ h D Φ Cphase hd hh hhom hCphase hCsource htarget hsmooth hdiff hdiag
    I g charts hgr hderiv hnorm hcover hbuffer
  refine ⟨?_, ?_⟩
  · exact congrArg (extendedProjectedStress extension) (hsame F)
  · have hthird (a : ℝ) : 3 * (a / 3) = a := by ring
    simpa only [SelectedSectorNestedMaskConclusion, hthird] using hconstruct Q hQ (hbudget (lift F)) Φ Cphase hd hh hhom hCphase hCsource
      htarget hsmooth hdiff hdiag I g charts
      (fun j ↦ by have := hgr j; linarith) hderiv hnorm hcover
      (fun p hp ξ hξ ↦ interior_subset ((hbuffer p hp hξ).1))

end JanetCartan.ArbitraryAccuracy.SelectedSectorProtection
