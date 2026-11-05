module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Construction.InitializedAnalyticData.SignedFiniteFamily
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.CompleteSourcePlateau
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.SectorCapAdmission

/-!
# A terminal envelope family admitting both original source signs

The common initializer already chooses its full Q/B cap before the reference.
This leaf applies the actual finite selector at that supplied cap, retains its
full-source stationary witnesses, and collects the actual source tolerance.
Both terminal signs have the literal normalized plateau on the same family.
The consumer is the normalized initialized inverse continuation; no second cap,
reference or family is selected to replace its existing witnesses.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FixedDomainInverse
open RegularSector RegularSector.FiniteAlgebraic
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
open FullSourceStationary UniformEvolution

/-- Apply the complete finite selector at the initializer's already fixed Q/B
cap, retaining the same full-source incidence witnesses and one positive source
margin on every original state ball. The actual complete source has its plateau
around both terminal signs. This supplies the family and finite source tolerance
for `exists_common_initialized_normalized_smooth_inverse`; original source
supports and relative terminal geometry are the geometric inputs
(`new:sec:order-of-choices`, `app:ch_regular:thm:no-return`,
`app:ch_response:eq:fixed-factor-transfer`, `resolved-angular-tail`). -/
theorem exists_signed_terminal_envelope_family_of_coefficient_cap
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
    {M : ℝ} (hM : 0 ≤ M) :
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
      εcarrier ≤ chart.bufferRadius / 8 ∧ chart.maskRadius ≤ εcarrier ∧
      tsupport (f.angularMask center ∘ physicalCoordinates chart.index) ∩ sphere (0 : E) 1 ⊆
        fullAngularCone chart.radialSection (coordinateSplit chart.index ξ).2
          (εcarrier / 4) (aperture / 2) ∧
    let z := ((coordinateSplit chart.index x).1, ((coordinateSplit chart.index x).2,
      (coordinateSplit chart.index ξ).2))
    MapsTo (primaryCoordinateChange chart.index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z (εcarrier / 2)) ∧
    ∃ gradientLower > (0 : ℝ), gradientLower ≤ 1 ∧
    ∃ gradientUpper : ℝ, 1 ≤ gradientUpper ∧
    (∀ (Q : E → Coeff), cNorm (closedBall x RQ) 3 Q ≤ M →
      ∀ (h : RootState (Euclidean d) → ℝ)
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph TC TC),
      closedBall (z.1, z) chart.targetRadius ⊆ C.target →
      ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
      (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
      (∀ v ∈ closedBall (z.1, z) chart.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1 / 2) →
      (∀ j, cNorm (closedBall (z.1, z) chart.targetRadius) j (twoTimePhase C) ≤
        chart.phaseCost j * (1 + cNorm (closedBall x RQ) (j + 1) Q)) →
      ∀ t ∈ Icc (0 : ℝ) εcarrier, ∀ y ∈ elapsedPhysicalBox z (εcarrier / 2),
      ∀ ζ ∈ retainedFrequencyDomain chart.radialSection z εcarrier aperture (1 / 2),
        gradientLower * ‖ζ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase chart.radialSection C) t v ζ) y‖ ∧
        ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase chart.radialSection C) t v ζ) y‖ ≤ gradientUpper * ‖ζ‖) ∧
    ∃ amplitudeLo > (0 : ℝ), ∃ amplitudeHi > amplitudeLo,
    ∀ negative : Bool, ∀ j : ι,
    let sourcePhase := fun Q ↦ if negative then
      (T j).negativeFullSourcePhaseInCoordinates chart.index Q else
      (T j).fullSourcePhaseInCoordinates chart.index Q
    let sourceGradient := fun Q y ζ ↦ if negative then
      -(LeadingWave.FullModulation.phaseGradient (T j) Q y ζ) else
      LeadingWave.FullModulation.phaseGradient (T j) Q y ζ
    let sourceCovector := fun c : Param ↦ if negative then
      -((T j).reference.covector (0, c.2)) else (T j).reference.covector (0, c.2)
    ∃ V : Set Param, IsOpen V ∧ IsCompact (closure V) ∧
      (∀ c ∈ closure V,
        c.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter (T j)) (T j).family.radius) ∧
      sourceMargin ≤ (T j).family.threshold ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
          scale • sourceGradient Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.conicMask (f.angularMask center)) → c ∈ V) ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
        ∀ y ∈ Xsrc j, ∀ c ∈ Csrc j, ∀ scale : ℝ, 0 < scale →
        ∀ L : ℝ, 0 < L →
          scale • sourceGradient Q y c.2 ∈
            tsupport (RegularSector.FiniteMasks.dilatedConicMask (f.angularMask center) L) → c ∈ V) ∧
    ∃ sourceLower sourceUpper : ℝ, 0 < sourceLower ∧ sourceLower < sourceUpper ∧
      (∀ Q, cNorm (closedBall (0 : E) (T j).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress (d + 1)) < sourceMargin →
        ∀ q ∈ closure (elapsedPhysicalBox z εcarrier) ×ˢ closure V,
          sourceLower ≤ ‖fderiv ℝ (fun y ↦ sourcePhase Q y q.2) q.1‖ ∧
          ‖fderiv ℝ (fun y ↦ sourcePhase Q y q.2) q.1‖ ≤ sourceUpper) ∧
    ∃ envelopeGap > (0 : ℝ), ∃ envelopeRadius > (0 : ℝ),
      envelopeGap ≤ gap ∧ radius ≤ envelopeRadius ∧
      envelopeGap ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
        (sourceLower / (2 * gradientUpper)) ∧
      4 * sourceUpper / gradientLower ≤ envelopeRadius ∧
      (∀ c₀ ∈ Csrc j,
        envelopeGap ≤ retainedSelectorGap z.2.2 (εcarrier / 2) aperture
          ((‖sourceCovector c₀‖ / 2) / (2 * gradientUpper)) ∧
        4 * (2 * ‖sourceCovector c₀‖) / gradientLower ≤ envelopeRadius) ∧
    ∃ ρ > (0 : ℝ), ∃ g > (0 : ℝ), ∃ Rad > (0 : ℝ),
    ∃ InvBound > (0 : ℝ),
      amplitudeLo ≤ g / 2 ∧ g + 1 + (1 + ‖chart.radialSection‖) * Rad ≤ amplitudeHi ∧
      let O := retainedOpenAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture g Rad
      let D := retainedOpenIntegrationDomain z εcarrier O
      let U₀ := elapsedPhysicalBox z (εcarrier / 2) ×ˢ V
      IsOpen O ∧ Convex ℝ O ∧ IsCompact (closure O) ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture gap radius ⊆ O ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture
        envelopeGap envelopeRadius ⊆ O ∧
      retainedAnnularFrequencyCarrier chart.radialSection z.2.2 (εcarrier / 2) aperture
        (retainedSelectorGap z.2.2 (εcarrier / 2) aperture (sourceLower / (2 * gradientUpper)))
        (2 * (2 * sourceUpper / gradientLower)) ⊆ O ∧
      (∀ c ∈ closure V, primaryCoordinateChange chart.index (sourceCovector c) ∈ O) ∧
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
          (fullSourceJointPhase adj (curriedPhase chart.radialSection C) (sourcePhase Q))
          ((Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ×ˢ D) ∧
        ContDiffOn ℝ ∞ (κ adj) (Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀) ∧
        (∀ q ∈ U₀, κ adj (0, q) = WithLp.toLp 2
          (q.1, gradient (fun y ↦ sourcePhase Q y q.2) q.1)) ∧
        ∀ p ∈ Ioo (-2 * τ center) (2 * τ center) ×ˢ U₀,
          κ adj p ∈ D ∧
          gradient (fun w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (sourcePhase Q) (p, w)) (κ adj p) = 0 ∧
          fullSourceJointPhase adj (curriedPhase chart.radialSection C)
            (sourcePhase Q) (p, κ adj p) = 0 ∧
          dist (κ adj p) (WithLp.toLp 2
            (p.2.1, gradient (fun y ↦ sourcePhase Q y p.2.2) p.2.1)) ≤ ρ / 2 ∧
          (∀ w ∈ closure D,
            let f := fun q w ↦ fullSourceJointPhase adj (curriedPhase chart.radialSection C)
              (sourcePhase Q) ((p.1, q), w)
            IsUnit (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w) ∧
              ‖Ring.inverse (averagedPhaseHessian f (fun q ↦ κ adj (p.1, q)) p.2 w)‖ ≤ InvBound) ∧
          ∀ w ∈ closure D, ∀ u ∈ uIcc (0 : ℝ) p.1, ∀ v ∈ Icc (0 : ℝ) 1,
            ((u, p.2), κ adj p + v • (w - κ adj p)) ∈ fullSourceSignedCarrier z εcarrier (closure V) O ∧
            ∀ o : Bool, fullSourceGraphPoint o ((u, p.2), κ adj p + v • (w - κ adj p)) ∈
              domain chart.radialSection C.target)
 := by
  classical
  obtain ⟨hzero, hregular, aperture, hAp, hApξ, θ, hθ, hbuffer⟩ :=
    protected_terminal_compact_selection_data hd hin hout hnest hsym hbad
  let envelopeAperture := 2 * aperture
  have hApE : 0 < envelopeAperture := by dsimp [envelopeAperture]; positivity
  have hApHalf : ∀ ξ ∈ Γout, ∀ i, |ξ i| < envelopeAperture / 2 := by
    intro ξ hξ i
    simpa only [envelopeAperture, mul_div_cancel_left₀ aperture (by norm_num : (2 : ℝ) ≠ 0)]
      using hApξ ξ hξ i
  have hApWhole : ∀ ξ ∈ Γout, ∀ i, |ξ i| < envelopeAperture := by
    intro ξ hξ i
    exact (hApHalf ξ hξ i).trans (half_lt_self hApE)
  obtain ⟨f, hcollars, τ, hτ, hstationary⟩ :=
    exists_actualMaskFamily_with_signed_full_source_envelope_margins
      P T hframe Csrc hCsrc hcsrc Xsrc hXsrc hsource hΩ x hRQ hKΩ hKprimary
      hout hzero hregular hM hApE hgap (radius := radius) hApHalf hM
  choose hmaskτ hinterval εcarrier hεcarrier hεL hεb hεbuffer hmaskε hcone hphysical
    gradientLower hgradLo hgradLoOne gradientUpper hgradHi hfrequency
    amplitudeLo hamplitudeLo amplitudeHi hamplitudeHi hincidence using hstationary
  choose V hV hVK hparam δ hδ hδT hcapture hcaptureDil hrest using hincidence
  obtain ⟨sourceMargin, hmargin, hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : f.centers × (Bool × ι) ↦ (0 : ℝ))
    (y := fun p ↦ δ p.1 p.2.1 p.2.2) (fun p ↦ hδ p.1 p.2.1 p.2.2)
  have hmarginle (p : f.centers) (negative : Bool) (j : ι) : sourceMargin ≤ δ p negative j := by
    simpa using (hsmall (p, negative, j)).le
  refine ⟨envelopeAperture, hApE, hApWhole, θ, hθ, hbuffer, f, ?_, hcollars,
    sourceMargin, hmargin, τ, hτ, ?_⟩
  · intro ξ hξ
    exact complete_source_plateau_on_outer_terminal_buffer hout hsym f
      (union_subset (hbuffer ξ hξ).1 (hbuffer ξ hξ).2)
  · intro p
    refine ⟨hmaskτ p, hinterval p, εcarrier p, hεcarrier p, hεL p, hεb p,
      hεbuffer p, hmaskε p, hcone p, hphysical p,
      gradientLower p, hgradLo p, hgradLoOne p, gradientUpper p, hgradHi p, hfrequency p,
      amplitudeLo p, hamplitudeLo p, amplitudeHi p, hamplitudeHi p, ?_⟩
    intro negative j
    refine ⟨V p negative j, hV p negative j, hVK p negative j, hparam p negative j, (hmarginle p negative j).trans (hδT p negative j), ?_, ?_, ?_⟩
    · intro Q hQ
      exact hcapture p negative j Q (hQ.trans_le (hmarginle p negative j))
    · intro Q hQ
      exact hcaptureDil p negative j Q (hQ.trans_le (hmarginle p negative j))
    obtain ⟨sourceLower, sourceUpper, hsourceLo, hsourceHi, hsourceBand,
      envelopeGap, hgapE, envelopeRadius, hradiusE, hgapOrig, hradiusOrig, hgapBand, hradiusBand, hselector,
      ρ, hρ, g, hg, Rad, hRad, InvBound, hInvBound, hamplo, hamphi,
      hO, hOc, hOK, hFO, hEnvelopeFO, hfreq, hmaps⟩ := hrest p negative j
    refine ⟨sourceLower, sourceUpper, hsourceLo, hsourceHi,
      (fun Q hQ ↦ hsourceBand Q (hQ.trans_le (hmarginle p negative j))),
      envelopeGap, hgapE, envelopeRadius, hradiusE, hgapOrig, hradiusOrig, hgapBand, hradiusBand, hselector,
      ρ, hρ, g, hg, Rad, hRad, InvBound, hInvBound, hamplo, hamphi,
      hO, hOc, hOK, hFO, hEnvelopeFO, ?_, hfreq, ?_⟩
    · apply (retainedAnnularFrequencyCarrier_mono _ _ _ _ hgapBand ?_).trans hEnvelopeFO
      calc
        2 * (2 * sourceUpper / gradientLower p) = 4 * sourceUpper / gradientLower p := by ring
        _ ≤ envelopeRadius := hradiusBand
    · intro Q hQstate hQcoeff hQlow
      exact hmaps Q hQstate hQcoeff (hQlow.trans_le (hmarginle p negative j))

end JanetCartan.FixedDomainInverse
