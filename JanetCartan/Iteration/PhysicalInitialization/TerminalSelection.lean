module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CappedSelection
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompleteSourcePlateau
public import JanetCartan.Iteration.PhysicalInitialization.Admission

/-!
# The actual terminal family before the physical common reference

The original relative no-return constructor supplies the protected sectors on
its fixed cover and quantitative family. The actual sector-history cap is chosen
first; capped full-source incidence selection then supplies one finite family.
A finite minimum of its actual phase margins fixes the full-array reference
admission tolerance. The larger terminal compact supplies the literal normalized
source plateau for the same family at both terminal orientations.

This physical variant uses the checked pre-reference Q/full-B cap and the real
Schwartz history admission. Every retained collar, stationary constant and source
plateau is constructed by the original generic finite selector; the global
increments are never periodized. Parent initialization still applies the returned
finite full-array margin to its same original reference callback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu
open Characteristic Characteristic.AlgebraicChart Characteristic.RootFamily
open Characteristic.ResidualCoordinates Characteristic.AlgebraicSymbols
open Characteristic.EvolutionIntegral Characteristic.AmplitudeBounds
open Characteristic.ConicPhase Characteristic.EvolutionIntegral.KernelIdentification
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open HamiltonPhase CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ArbitraryAccuracy
open NormalizedSolver FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ} {ι : Type*} [Finite ι]
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (P : ι → Patch (d + 1)) (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
local notation "E" => Euclidean (d + 1)
local notation "TC" => Characteristic.TwoTimePoint (Euclidean d)
local notation "W" => CarrierVariables (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)
open FullSourceStationary

/-- Apply the actual capped finite selector to the original larger terminal
compact, then collect its actual source margins and the SAME family's coefficient
radius before reference initialization. The relative producer
`exists_primitive_signed_complete_source_terminal_cover` supplies exactly these
sectors and the positive reference protection margin on the supplied `D,T`.
The original CarrierData constructor
`exists_common_normalized_history_reference_with_chart_centers_and_carrier_data_and_comparison_radius_and_position_smoothness`
consumes the returned tolerance in its arbitrary finite full/extended-margin
clause, with `orders = {max m (sectorLowOrder d)}` on that same menu and scale.
No reference is selected here. Every original collar, complete stationary
interval, full independent source covector, and both terminal signs remain on
one `f` (`app:ch_regular:thm:no-return`, `app:ch_response:eq:fixed-factor-transfer`,
`resolved-angular-tail`, `new:sec:order-of-choices`). -/
theorem exists_pre_reference_terminal_mask_family_physical
    (hframe : ∀ j, closedBall (0 : E) (T j).data.localReference.stateRadius ⊆ U)
    (Csrc : ι → Set Param) (hCsrc : ∀ j, IsCompact (Csrc j))
    (hcsrc : ∀ j c, c ∈ Csrc j →
      c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius)
    (Xsrc : ι → Set E) (hXsrc : ∀ j, IsCompact (Xsrc j))
    (hsource : ∀ j, Xsrc j ×ˢ Csrc j ⊆ LeadingWave.FullModulation.domain (T j))
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hKprimary : ∀ j, closedBall x RQ ⊆ ball 0 (T j).physicalRadius)
    (hd : 5 ≤ d + 1) {Γin Γout : Set E}
    (hin : IsCompact Γin) (hout : IsCompact Γout)
    (hnest : Γin ⊆ interior Γout) (hsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    (hbad : Γout ⊆ (cubeBadSubspaceUnion (d+1))ᶜ)
    {gap radius : ℝ} (hgap : 0 < gap)
    (ext : BallExtension.Parameters E) (hext : ext.center = 0)
    {b R : ℝ} (heb : ext.radius ≤ b) (hbR : b < R)
    (m : ℕ) (hm : 6 ≤ m) {ηprotect : ℝ} (hprotect : 0 < ηprotect) :
    ∃ M > (0 : ℝ),
    ∃ aperture > (0 : ℝ), (∀ ξ ∈ Γout, ∀ i, |ξ i| < aperture) ∧
    ∃ θ > (0 : ℝ), (∀ ξ ∈ Γin,
      closedBall ξ θ ⊆ interior Γout ∧ closedBall (-ξ) θ ⊆ interior Γout) ∧
    ∃ f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) Γout M,
      (∀ ξ ∈ Γin,
        (closedBall ξ θ ∪ closedBall (-ξ) θ ⊆
          interior {η | gammaTotal f hout η = 1}) ∧
        ∀ L > (0 : ℝ), ∀ ζ : E,
          NormedSpace.normalize ζ ∈ closedBall ξ θ ∪ closedBall (-ξ) θ →
          normalizedSourceMask f hout L ζ + physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1 ∧
          (4*L ≤ ‖ζ‖ → normalizedSourceMask f hout L ζ = 1)) ∧ (∀ p : f.centers,
      let c := f.chart p
      let ξ := p.val.val
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 ∧
      RootBuffer c.index c.row c.col (cubeStress (d + 1)) ξ c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
        (closedBall x RQ) ∧
    ∃ evolutionTime speedGap rootSize rootCost,
      LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost ∧
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
      a < c.coefficientRadius ∧ b < min c.coefficientRadius c.rootRadius ∧
      let KA := closedBall (cubeStress (d + 1)) a
      let Kη := closedBall (coordinateSplit c.index ξ).2 b
      let x' := (physicalCoordinates c.index).symm x
      IsCompact KA ∧ IsCompact Kη ∧
      KA ⊆ ball (cubeStress (d + 1)) c.coefficientRadius ∧
      Kη ⊆ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) ∧
      (∀ p ∈ ball (cubeStress (d + 1)) c.coefficientRadius ×ˢ
        ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius),
        ContDiffAt ℝ ∞ c.root p) ∧
      (∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ c.root p) ∧
    ∃ bound > (0 : ℝ),
      (∀ p ∈ KA ×ˢ Kη,
        ‖coefficientRootPencil (coordinateSplit c.index) c.root p‖ ≤ bound ∧
        ‖pencil p.1 ((coordinateSplit c.index).symm (1, 0))‖ ≤ bound ∧
        (coefficientRootPencil (coordinateSplit c.index) c.root p).det = 0 ∧
        c.minorGap ≤ |(coefficientRootPencil (coordinateSplit c.index) c.root p).adjugate c.row c.col| ∧
        c.transportGap ≤ |minorTransportCoefficient
          (coefficientRootPencil (coordinateSplit c.index) c.root p)
          (pencil p.1 ((coordinateSplit c.index).symm (1, 0))) c.row c.col|) ∧
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass c.row c.col bound c.minorGap c.transportGap,
        ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 c.row c.col)
          (minorLeftNullvector p.1 p.2 c.row c.col) e).det|) ∧
      (minorCoefficientClass c.row c.col bound c.minorGap c.transportGap ×ˢ
        closedBall (0 : ℝ) ε ⊆ minorComplementDomain c.row c.col) ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ a' ≤ c.coefficientRadius ∧
      f.coefficientRadius ≤ a' ∧
    ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ c.angularNeighborhood ∧
      tsupport (f.angularMask p) ⊆ V ∧
      (∀ ζ ∈ V, ∀ t : ℝ, 0 < t → t • ζ ∈ V) ∧
    ∃ Λ > (0 : ℝ),
      (∀ ζ ∈ V,
        let ζ' := (physicalCoordinates c.index).symm ζ
        0 < c.radialSection (spatialPart ζ') ∧
        spatialPart (normalizeCovector c.radialSection ζ') ∈ Kη ∧
        ‖normalizeCovector c.radialSection ζ'‖ ≤ Λ ∧
        ∀ A ∈ closedBall (cubeStress (d + 1)) a',
          |normalizeCovector c.radialSection ζ' 0 -
            c.root (A, spatialPart (normalizeCovector c.radialSection ζ'))| ≤ ε) ∧
      ∀ Q : E → Coeff, MapsTo Q Ω (closedBall (cubeStress (d + 1)) a') →
        (∀ β : E → ℂ, tsupport β ⊆ V →
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹' Ω) ε (β ∘ physicalCoordinates c.index) ∧
          NormalizedSpectralSupport c.radialSection (fieldRoot (coordinateSplit c.index) Q c.root)
            (physicalCoordinates c.index ⁻¹'
              (rootPhysicalPosition (coordinateSplit c.index) '' tsupport c.sourceMask))
            ε (β ∘ physicalCoordinates c.index) ∧
          (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
            (normalizeCovector c.radialSection '' tsupport (β ∘ physicalCoordinates c.index)) ⊆
            complementDomain c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col (fieldDomain (coordinateSplit c.index) Ω c.radialSection
                (coordinateSplit c.index ξ).2 c.coefficientRadius)) ∧
        (ContDiffOn ℝ ∞ Q Ω → ∀ ζ ∈ V,
          let ζ' := normalizeCovector c.radialSection ((physicalCoordinates c.index).symm ζ)
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') y) ∧
          ∀ m, cNorm (closedBall x' RQ) m
            (fun y ↦ bminus c.index Q (fieldRoot (coordinateSplit c.index) Q c.root)
              c.row c.col y ζ') ≤ C m * (1 + cNorm (closedBall x RQ) m Q))) ∧
    ∃ sourceMargin > (0 : ℝ),
    ∃ τ : f.centers → ℝ, (∀ center, 0 < τ center) ∧
    (∀ center : f.centers,
      let chart := f.chart center
      let ξ := center.val.val
      chart.maskRadius ≤ τ center ∧
      Icc (0 : ℝ) (3 * chart.maskRadius / 4) ⊆ Ioo (-2 * τ center) (2 * τ center) ∧
    ∃ εcarrier > (0 : ℝ), εcarrier ≤ chart.rootRadius ∧ 4 * εcarrier ≤ chart.targetRadius ∧
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index ξ).2))
    MapsTo (primaryCoordinateChange chart.index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z (εcarrier / 2)) ∧
    ∀ j : ι,
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius) ∧
      sourceMargin ≤ (T j).family.threshold ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
          scale • LeadingWave.FullModulation.phaseGradient (T j) Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.conicMask (f.angularMask center)) → c ∈ V) ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
        ∀ L : ℝ, 0 < L →
          scale • LeadingWave.FullModulation.phaseGradient (T j) Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.dilatedConicMask (f.angularMask center) L) → c ∈ V) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ InvBound > (0 : ℝ),
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      (∀ c ∈ closure V, primaryCoordinateChange chart.index ((T j).reference.covector (0, c.2)) ∈ O) ∧
      ∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 4 Q.1 ≤ M →
        cNorm (closedBall x RQ) 4 Q.1 ≤ M →
        cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
      ∀ (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC) (a : ℝ),
        (C : TC → TC) = twoTimeProjection Φ →
        C.source = ball (z.1, z) a → (∀ v ∈ ball z a, Φ (v, 0) = v) →
        closedBall (z.1, z) chart.targetRadius ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        (∀ m, cNorm (closedBall (z.1, z) chart.targetRadius) m (twoTimePhase C) ≤
          chart.phaseCost m * (1 + cNorm (closedBall x RQ) (m + 1) Q.1)) →
      a ≤ chart.rootRadius →
      closedBall z chart.rootRadius ⊆ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius →
      (∀ w ∈ fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius,
        ∀ t : ℝ, 0 < t → fieldRoot (coordinateSplit chart.index) Q.1 chart.root (w.1, (w.2.1, t • w.2.2)) =
          t * fieldRoot (coordinateSplit chart.index) Q.1 chart.root w) →
      (∀ v ∈ C.target, twoTimeState Φ (C.symm v) ∈
          fieldDomain (coordinateSplit chart.index) Ω chart.radialSection (coordinateSplit chart.index ξ).2 chart.coefficientRadius ∧
        (twoTimeState Φ (C.symm v)).1 = v.1) →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C)
        (twoTimePhaseDifferential (fieldRoot (coordinateSplit chart.index) Q.1 chart.root) Φ C v) v) →
      ∃ κ : Bool → Par → W, ∀ adj : Bool,
        ContDiffOn ℝ ∞
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C) ((T j).fullSourcePhaseInCoordinates chart.index Q))
          ((Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            ((T j).fullSourcePhaseInCoordinates chart.index Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ (T j).fullSourcePhaseInCoordinates chart.index Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              ((T j).fullSourcePhaseInCoordinates chart.index Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z εcarrier (closure V) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain chart.radialSection C.target) ∧
    ∃ η > (0 : ℝ),
      ∀ G₀ Gref : FlatReference (d+1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Gref.map = sourceDilation G₀.map ρ → R < G₀.domain.chartRadius →
      cNorm (closedBall (0 : E) b) (max m (sectorLowOrder d))
        (geometricReducedCoefficients Gref.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      (∀ i, cNorm (closedBall (0 : E) b) m
        (fun y ↦ ProjectedStressFrame.projectedStress Gref.map y i - cubeStress (d+1) i) < ηprotect) ∧
      ∀ {Cband : ℝ}, 1 ≤ Cband →
       ∀ rStar kMin : ℕ, 8 ≤ rStar → sectorLowOrder d + 2 ≤ rStar →
      RevisedScales.displacementLoss (d+1) +
        bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap Gref.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d+1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ A : Set E, cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < sourceMargin) ∧
      ∀ A : Set E, IsCompact A →
        cNorm A (sectorLowOrder d) Q ≤ M ∧
        cNorm A (sectorLowOrder d) B ≤ M ∧ cNorm A 4 Q ≤ M := by
  classical
  obtain ⟨M, hM, hadmission⟩ :=
    PhysicalInitialization.exists_terminal_physical_admission_on_source_dilation ext hext heb hbR m hm
  obtain ⟨hzero, hregular, aperture, hAp, hApξ, θ, hθ, hbuffer⟩ :=
    protected_terminal_compact_selection_data hd hin hout hnest hsym hbad
  obtain ⟨f, hcollars, τ, hτ, hstationary⟩ :=
    exists_actualMaskFamily_with_full_source_incidence_radii_of_coefficient_cap
      P T hframe Csrc hCsrc hcsrc Xsrc hXsrc hsource hΩ x hRQ hKΩ hKprimary
      hout hzero hregular hM.le hAp hgap (radius := radius) hApξ hM.le
  choose hmaskτ hinterval εcarrier hεcarrier hεL hεb hphysical hincidence using hstationary
  choose V hV hVK hparam δ hδ hδT hcapture hcaptureDil hrest using hincidence
  obtain ⟨sourceMargin, hmargin, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : f.centers × ι ↦ (0 : ℝ))
    (y := fun p ↦ δ p.1 p.2) (fun p ↦ hδ p.1 p.2)
  have hmarginle (p : f.centers) (j : ι) : sourceMargin ≤ δ p j := by
    simpa using (hsmall (p, j)).le
  obtain ⟨η, hη, hadmit⟩ := hadmission f Unit inferInstance
    (fun _ ↦ sourceMargin) (fun _ ↦ hmargin) ηprotect hprotect
  refine ⟨M, hM, aperture, hAp, hApξ, θ, hθ, hbuffer, f, ?_, hcollars,
    sourceMargin, hmargin, τ, hτ, ?_, η, hη, ?_⟩
  · intro ξ hξ
    exact complete_source_plateau_on_outer_terminal_buffer hout hsym f
      (union_subset (hbuffer ξ hξ).1 (hbuffer ξ hξ).2)
  · intro p
    refine ⟨hmaskτ p, hinterval p, εcarrier p, hεcarrier p, hεL p, hεb p, hphysical p, ?_⟩
    intro j
    refine ⟨V p j, hV p j, hVK p j, hparam p j, (hmarginle p j).trans (hδT p j), ?_, ?_, ?_⟩
    · intro Q hQ
      exact hcapture p j Q (hQ.trans_le (hmarginle p j))
    · intro Q hQ
      exact hcaptureDil p j Q (hQ.trans_le (hmarginle p j))
    obtain ⟨ρ, hρ, g, hg, Rad, hRad, InvBound, hInvBound, hO, hOc, hOK, hFO, hfreq, hmaps⟩ := hrest p j
    refine ⟨ρ, hρ, g, hg, Rad, hRad, InvBound, hInvBound, hO, hOc, hOK, hFO, hfreq, ?_⟩
    intro Q hQstate hQcoeff hQlow
    exact hmaps Q hQstate hQcoeff (hQlow.trans_le (hmarginle p j))
  · intro G₀ Gref ρ hρ hρone hsame hR href
    obtain ⟨hrow, hhistory⟩ := hadmit G₀ Gref ρ hρ hρone hsame hR href
    refine ⟨hrow, ?_⟩
    intro Cband hband rStar kMin hStar hreserve horder
    obtain ⟨S, hS, hcurrent⟩ := hhistory hband rStar kMin hStar hreserve horder
    refine ⟨S, hS, ?_⟩
    intro R₀ hR₀ s u ell hu
    obtain ⟨hQ, hB, hrange, hphase, hcap⟩ := hcurrent R₀ hR₀ s u ell hu
    exact ⟨hQ, hB, hrange, hphase (), hcap⟩

end JanetCartan.RegularSector.FiniteAlgebraic
