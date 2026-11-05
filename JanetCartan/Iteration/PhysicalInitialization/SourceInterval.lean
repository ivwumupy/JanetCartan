module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Construction.InitializedAnalyticData.SignedTerminalFamily

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedSmooth.Construction
public import JanetCartan.Iteration.PhysicalInitialization.TerminalSelection
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation

/-!
# A regular inverse throughout one prescribed source interval

The source reference is fixed before the finite regular family. The final
reference is not: after selecting the actual terminal masks and normalized
inverse, the proved full-array dilation estimate supplies the missing finite
margin on every sufficiently small contraction of that SAME source reference.
No reference is selected again, no full-array margin is assumed, and the cap is
strictly below any previously prescribed positive source-inverse cap. All
operator constants and this cap precede physical histories and the target.

The original source/terminal geometry is still supplied by the common original
initializer. The construction below closes its finite-reference-margin input,
not the other analytic producers of the complete main theorem.
Consumers: the same-source initialization and physical signed/primary response.
Sources: `new:sec:order-of-choices`, `main:prop:seed`,
`app:ch_regular:eq:exact-physical`, `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 24000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius NNReal ENNReal
namespace JanetCartan.FixedDomainInverse
open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.NormalizedSolver RegularSector.EllipticComplement
open Characteristic Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.ConicAmplitude Characteristic.AmplitudeBounds Characteristic.RootFamily
open Characteristic.ConicPhase Characteristic.UniformAmplitudes Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
open FinitePdo FiniteEvolution FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev SmallSupport
open FiniteResidual.FiniteIdentity CoefficientNorms
open ActualCarriers Characteristic.AlgebraicChart Characteristic.AlgebraicSymbols
open Characteristic.PdoRealization FiniteAlgebraic AmplitudeBound
open ArbitraryAccuracy.ResidualLocalization ResponseTransfer.Complement
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "TPoint" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))

open ActualCarriers.CurrentFullPhase FrozenMenu
open HamiltonPhase CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors ResponseTransfer.DirectEvolution
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ArbitraryAccuracy
open FullSourceStationary FourierIntegral.LowBounds.FrequencyCutoff
variable {ι : Type*} [Finite ι] {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (P : ι → Patch (d+1)) (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
local notation "TC" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Par" => ℝ × (E × Param)

/-- Construct the actual regular family and its normalized smooth inverse,
then satisfy its full-array reference margin on a whole interval of the SAME
source dilations. This removes the analytic reference-margin premise of the
pre-reference inverse while retaining an arbitrary supplied positive source cap.
The output applies to any already designated `Gref` with the literal scaled
map; it does not introduce another existential reference. All coefficient and
operator fields are constructed, and the physical histories retain their
original real Schwartz Fourier budgets (`main:prop:seed`,
`app:ch_regular:eq:exact-physical`, `new:sec:order-of-choices`). -/
theorem exists_terminal_physical_inverse_on_source_interval
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
    (m : ℕ) (hm : 6 ≤ m) {ηprotect : ℝ} (hprotect : 0 < ηprotect)
    {κ : ℝ} (hκ₀ : 0 < κ) (hκ₁ : κ < 1)
    (G₀ : FlatReference (d+1)) (hR : R < G₀.domain.chartRadius)
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap) :
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
      ∃ κ : Bool → Par → CarrierVariables (d+1), ∀ adj : Bool,
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
              domain chart.radialSection C.target) ∧
    ∃ η > (0 : ℝ),
    ∃ (evolutionTime speedGap rootSize : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ),
      (∀ p, LocalProtectionCertificate (f.chart p) (evolutionTime p) (speedGap p)
        (rootSize p) (rootCost p)) ∧
      (∀ p, 0 < 6 * f.physicalRadius ∧
        6 * f.physicalRadius < (f.chart p).sourceRadius ∧
        6 * f.physicalRadius < evolutionTime p) ∧
      (∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) ∧
      (∀ p : f.centers, SelectedChartPhysicalEvolution (f.chart p) (f.angularMask p)
        ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
        ((physicalCoordinates (f.chart p).index) ⁻¹' Ω)) ∧
      (∀ p : f.centers,
        let c := f.chart p
        RootBuffer c.index c.row c.col (cubeStress (d+1)) p.val.val c.root c.coefficientRadius c.rootRadius
          c.minorGap c.transportGap ∧
        MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
          (closedBall x RQ) ∧
        ∃ ε > (0 : ℝ), ∃ Rbox > (0 : ℝ), ∃ Mbound > (0 : ℝ),
        ∃ C D G : ℕ → ℝ, (∀ m, 0 < C m) ∧ (∀ m, 1 ≤ D m) ∧ (∀ n, 0 ≤ G n) ∧
        ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          MapsTo Q Ω (closedBall (cubeStress (d+1)) f.coefficientRadius) →
          cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
          cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
          let h := fieldRoot (coordinateSplit c.index) Q c.root
          let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
          let U := physicalCoordinates c.index ⁻¹' Ω
          let b := directAlgebraicSymbol
            (conicBminus c.radialSection c.index Q h c.row c.col)
            (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask) β
          let pb := physicalSymbolApply
            (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
            (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b
          NormalizedSpectralSupport c.radialSection h U ε β ∧
          ContDiffOn ℝ ∞ h (normalizedRootDomain c) ∧
          (∀ w ∈ normalizedRootDomain c, (rootPencil (coordinateSplit c.index) Q h w).det = 0) ∧
          (U ×ˢ (normalizeCovector c.radialSection '' tsupport β) ⊆
            complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) ∧
          (∀ ζ ∈ tsupport β, ∀ y ∈ U,
            (∑ a, (ζ a : ℂ) • (coefficient c.index Q y a).map Complex.ofReal) *
              conicBminus c.radialSection c.index Q h c.row c.col y ζ =
                1 - projector c.index Q h c.row c.col y
                  ((c.radialSection (spatialPart ζ))⁻¹ • spatialPart ζ)) ∧
          ∀ s ∈ ({b, pb} : Set (E → E → CMat)),
            ContDiff ℝ ∞ (Function.uncurry s) ∧
            GraphNormalAmplitudeBounds
              (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) s)
              Rbox Mbound ∧
            (∀ m ξ is, is.length ≤ m → ∀ z,
              (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
                (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) s ξ) z‖ ≤
                C m * (1 + cNorm (closedBall x RQ) (m+1) Q +
                  cNorm (closedBall x RQ) (m+1) B)) ∧
            ∀ n : ℕ,
              let T := physicalOperator c.index
                (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) s)
              let high := D (2 * (d+2) + (n+1)) *
                (1 + cNorm (closedBall x RQ) (n + (2 * (d+2) + 2)) Q +
                  cNorm (closedBall x RQ) (n + (2 * (d+2) + 2)) B)
              (∀ u : H, MemVectorFourierSobolev (n : ℝ) u →
              (MemVectorFourierSobolev ((n : ℝ)+1) (T u) ∧
                vectorFourierSobolevNorm ((n : ℝ)+1) (T u) ≤
                  ((d+1 : ℝ) * (d+1) * G n) *
                    (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖)) ∧
              (MemVectorFourierSobolev ((n : ℝ)+1) (T.adjoint u) ∧
                vectorFourierSobolevNorm ((n : ℝ)+1) (T.adjoint u) ≤
                  ((d+1 : ℝ) * (d+1) * G n) *
                    (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖))) ∧
              ∀ u : H,
                (MemVectorFourierSobolev (-(n : ℝ)) (T u) ∧
                  vectorFourierSobolevNorm (-(n : ℝ)) (T u) ≤
                    ((d+1 : ℝ) * (d+1) * ((d+1 : ℝ) * (d+1) * G n)) *
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u) ∧
                (MemVectorFourierSobolev (-(n : ℝ)) (T.adjoint u) ∧
                  vectorFourierSobolevNorm (-(n : ℝ)) (T.adjoint u) ≤
                    ((d+1 : ℝ) * (d+1) * ((d+1 : ℝ) * (d+1) * G n)) *
                      (1 + high) * vectorFourierSobolevNorm (-((n : ℝ)+1)) u)) ∧
    ∃ L : ℝ, ∃ hL : f.radialThreshold ≤ L,
    ∃ (angular : f.centers → Euclidean d → ℝ) (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) * χout p ((physicalCoordinates (f.chart p).index).symm y) =
        (output y : ℂ)) ∧
      (∀ p, SelectedChartEndpointAtWithProtection f p
        (evolutionTime p) (speedGap p) (rootSize p) (rootCost p) L (angular p) (χout p) (χsource p) (hs p) output) ∧
      (∀ p, selectedSourceSymbol (withEnlargedThreshold f L hL) p
        (withEnlargedThreshold f L hL).radialThreshold = selectedSourceSymbol f p (2*L)) ∧
    ∃ (base : Fin 2 → f.centers → ℝ) (cost : Fin 2 → f.centers → ℕ → ℝ)
      (maskCost : ℕ → ℝ) (Rbox : f.centers → ℝ)
      (Dpdo Dgain Gain : f.centers → ℕ → ℝ)
      (ra rb : f.centers → ℝ) (amplitudeCost : f.centers → ℕ → ℝ),
      (∀ o p, 0 < base o p) ∧ (∀ o p s, 0 < cost o p s) ∧
      (∀ s, 1 ≤ maskCost s) ∧ (∀ p, 0 < Rbox p) ∧
      (∀ p s, 1 ≤ Dpdo p s) ∧ (∀ p s, 1 ≤ Dgain p s) ∧ (∀ p s, 0 ≤ Gain p s) ∧
      (∀ p, 0 < ra p) ∧ (∀ p, ra p < rb p) ∧ (∀ p m, 0 < amplitudeCost p m) ∧
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) ∧
      (∀ p, FinitePdo.RetainedConstruction.DiagonalFrequencyCoverage
        (f.chart p).radialSection (coordinateSplit (f.chart p).index p.val.val).2
        ((f.chart p).bufferRadius/2) (ra p) (rb p) (selectedEndpointMultiplier f p L)) ∧
    ∃ completeCost : Fin 2 → ℕ → ℝ, (∀ o s, 0 ≤ completeCost o s) ∧
    ∃ completeLocalCost : ℝ, 0 ≤ completeLocalCost ∧
    ∃ (normRadius : ℝ) (hQR : RQ < normRadius)
      (hNormBall : closedBall x normRadius ⊆ Ω),
    ∃ coefficientCost : ℕ → ℝ, (∀ m, 1 ≤ coefficientCost m) ∧
      (∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
          (B : Euclidean (d + 1) → MetricTensor (d + 1))
          (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω),
        let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall Q hQ
        let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall B hB
        (∀ k, MemRestrictionSobolev (ball x normRadius) k uQ ∧
          MemRestrictionSobolev (ball x normRadius) k uB) ∧
        ∀ m,
          cNorm (closedBall x RQ) m Q ≤
            coefficientCost m * restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uQ ∧
          cNorm (closedBall x RQ) m B ≤
            coefficientCost m * restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uB ∧
          1 + cNorm (closedBall x RQ) m Q + cNorm (closedBall x RQ) m B ≤
            coefficientCost m * (1 + restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uQ +
              restrictionSobolevNorm (ball x normRadius) (m + (d + 2)) uB)) ∧
    ∃ hbudget : 0 ≤ 4*completeLocalCost,
    ∃ hrU : 0 < min r f.physicalRadius,
    ∃ hUW : ball x (min r f.physicalRadius) ⊆ ball x normRadius,
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : E → ℝ) ⊆ ball x (min r f.physicalRadius) ∧
      tsupport (χ₃ : E → ℝ) ⊆ ball x (min r f.physicalRadius) ∧
      (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) ∧
      (ball x χ₂.rIn).Nonempty ∧ IsOpen (ball x χ₂.rIn) ∧
      ball x χ₂.rIn ⊆ ball x (min r f.physicalRadius) ∧
      (∀ y ∈ ball x χ₂.rIn, χ₂ y = 1) ∧
      (∀ y ∈ ball x (min r f.physicalRadius), output y = 1 ∧ f.inputMask y = 1) ∧
    ∃ gainCost : ℕ → ℝ, (∀ s, 0 ≤ gainCost s) ∧
    ∃ correctionCost responseCost classicalCost : ℕ → ℝ,
      (∀ s, 0 ≤ correctionCost s) ∧ (∀ s, 0 ≤ responseCost s) ∧
      (∀ m, 1 ≤ classicalCost m) ∧
    ∃ sourceJetCost : ℕ → ℝ, (∀ s, 0 ≤ sourceJetCost s) ∧
      ∃ contractionCap : ℝ, 0 < contractionCap ∧ contractionCap < sourceCap ∧
      contractionCap ≤ 1 ∧ ∀ ρ ∈ Ioc (0 : ℝ) contractionCap,
      ∀ Gref : FlatReference (d+1), Gref.map = sourceDilation G₀.map ρ →
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
      ∃ (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B),
      MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ A : Set E, cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < sourceMargin) ∧
      (∀ A : Set E, IsCompact A →
        cNorm A (sectorLowOrder d) Q ≤ M ∧
        cNorm A (sectorLowOrder d) B ≤ M ∧ cNorm A 4 Q ≤ M) ∧
    ∃ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph TPoint TPoint)
      (G : f.centers → TPoint → ℝ) (Op : Fin 2 → f.centers → H →L[ℂ] H),
      (∀ p, SelectedProtectionData (f.chart p) (evolutionTime p) (speedGap p)
        (rootSize p) (rootCost p) Q (Φ p) (C p)) ∧
      (∀ p,
        let c := f.chart p
        let e := coordinateSplit c.index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        let h := fieldRoot e Q c.root
        let U := fieldDomain e Ω c.radialSection z.2.2 c.coefficientRadius
        let V := (C p).target ∩ (C p).symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
          (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2)))
        let Fs := selectedBufferedAmplitude f p Q B (Φ p) (C p)
        let W := selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
        ContDiffOn ℝ ∞ h U ∧
        (∀ w ∈ U, ∀ t : ℝ, 0 < t → h (w.1, (w.2.1, t • w.2.2)) = t*h w) ∧
        closedBall z c.rootRadius ⊆ U ∧
        (∀ w ∈ closedBall z c.rootRadius, (rootPencil e Q h w).det = 0 ∧
          c.minorGap ≤ |(rootPencil e Q h w).adjugate c.row c.col| ∧
          c.transportGap ≤ |minorTransportCoefficient (rootPencil e Q h w)
            (rootTimeCoefficient e Q w) c.row c.col|) ∧
        ((C p) : TPoint → TPoint) = twoTimeProjection (Φ p) ∧
        (C p).source = ball (z.1, z) c.sourceRadius ∧
        ContDiffOn ℝ ∞ (C p).symm (C p).target ∧
        closedBall (z.1, z) c.targetRadius ⊆ (C p).target ∧
        ContDiffOn ℝ ∞ (twoTimePhase (C p)) (C p).target ∧
        (∀ q ∈ (C p).target, HasFDerivAt (twoTimePhase (C p))
          (twoTimePhaseDifferential h (Φ p) (C p) q) q) ∧
        (∀ q ∈ (C p).target,
          ((C p).symm q).1 = q.1 ∧ ((C p).symm q).2.1 = q.2.1 ∧
          ((C p).symm q).2.2.2 = q.2.2.2 ∧
          (twoTimeState (Φ p) ((C p).symm q)).2.1 = q.2.2.1) ∧
        (∀ q ∈ (C p).target, twoTimeState (Φ p) ((C p).symm q) ∈ U ∧
          (twoTimeState (Φ p) ((C p).symm q)).1 = q.1) ∧
        (∀ w ∈ ball z c.sourceRadius, (w.1, w) ∈ (C p).target ∧
          (C p).symm (w.1, w) = (w.1, w) ∧
          twoTimePhase (C p) (w.1, w) = inner ℝ w.2.1 w.2.2) ∧
        (∀ q ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed (C p) q - 1‖ ≤ 1/2) ∧
        (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase (C p)) ≤
          c.phaseCost m * (1+cNorm (closedBall x RQ) (m+1) Q)) ∧
        ball (z.1, z) c.outerRadius ⊆ (C p).target ∧
        MapsTo (C p) (closedBall (z.1, z) c.maskRadius)
          (closedBall (z.1, z) (c.bufferRadius/2)) ∧
        ContDiff ℝ ∞ (G p) ∧
        (∀ t y η, G p (t, (t, (y, η))) = inner ℝ y η) ∧
        (∀ q ∈ tsupport (collared c.radialSection 0 (angular p) (Fs 0)) ∪
          tsupport (collared c.radialSection 1 (angular p) (Fs 1)),
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) →
          collared c.radialSection 1 (angular p) (Fs 2) q ≠ 0 →
          G p =ᶠ[𝓝 q] ConicPhase.phase c.radialSection (C p)) ∧
        (∀ y : E, c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
          WKB.firstOrderApply
            (fun x idx ↦ ((coefficient c.index Q x idx).map Complex.ofReal).mulVecLin)
            (fun x ↦ ((zeroth c.index B x).map Complex.ofReal).mulVecLin)
            (fun x ↦ Complex.exp (Complex.I * (G p (x 0, (s, (spatialPart x, η))) : ℂ)) •
              (fun k ↦ (W 0 + W 1) (x 0) s (spatialPart x) η k j)) y =
            Complex.exp (Complex.I * (G p (y 0, (s, (spatialPart y, η))) : ℂ)) •
              (fun k ↦ twoTimePhysicalApply
                (fun x idx ↦ (coefficient c.index Q x idx).map Complex.ofReal)
                (fun x ↦ (zeroth c.index B x).map Complex.ofReal) (W 1)
                  (y 0) s (spatialPart y) η k j)) ∧
        (∀ y : E, c.timeMask (y 0) = 1 → ∀ η,
          (coefficient c.index Q y 0).map Complex.ofReal * W 0 (y 0) (y 0) (spatialPart y) η =
            conicSourceSymbol c.radialSection (conicMask (angular p)) c.sourceMask y η •
              projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η)) ∧
        let Ψ := fun t s y η ↦ G p (t, (s, (y, η)))
        let a := (coordinateSplit c.index x).1-c.maskRadius/2
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 0 + W 1) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 0 (base 0 p) (cost 0 p) (Op 0 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (W 2) (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4) a Ψ
          (twoTimePhysicalApply (fun y idx ↦ (coefficient c.index Q y idx).map Complex.ofReal)
            (fun y ↦ (zeroth c.index B y).map Complex.ofReal) (W 1))
          (χout p) (χsource p) (selectedEndpointMultiplier f p L)
          (hs p) 1 (base 1 p) (cost 1 p) (Op 1 p) ∧
        EndpointPdoEstimates c.index (closedBall x RQ) Q B
          (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
          (selectedEndpointSymbol f p L Q (W 1)) (Rbox p) M (Dpdo p) (Dgain p) (Gain p) ∧
        (∀ q : TPoint, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
          (fun k ↦ collared c.radialSection 1 (angular p) (Fs 2) q k j) =
            WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
              (fun y k ↦ collared c.radialSection 1 (angular p) (Fs 1)
                (physicalSlice e q.2.1 q.2.2.2 y) k j) (e.symm (q.1, q.2.2.1))) ∧
        ∀ j : Fin 3,
          ContDiff ℝ ∞ (Fs j) ∧ HasCompactSupport (Fs j) ∧ tsupport (Fs j) ⊆ V ∧
          tsupport (Fs j) ⊆ closedBall (z.1, z) (c.bufferRadius/2) ∧
          ContDiff ℝ ∞ (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ∧
          tsupport (collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j)) ⊆
            ConicPhase.domain c.radialSection V ∧
          (∀ q : TPoint, q.2.1 ≤ z.1-c.maskRadius →
            collared c.radialSection (if j=0 then 0 else 1) (angular p) (Fs j) q = 0) ∧
          (∀ q ∈ V, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → Fs j =ᶠ[𝓝 q]
            pencilAmplitudeFamily c.index Q B h (Φ p) (C p) c.row c.col c.sourceMask j) ∧
          ∀ m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ∧
            twoTimeOrderSeminorm (if j=0 then 0 else 1)
              (bufferedJetSet c.radialSection z (c.bufferRadius/2) (ra p) (rb p)) m (W j) ≤
              amplitudeCost p m * (1+cNorm (closedBall x RQ) (m+10) Q+
                cNorm (closedBall x RQ) (m+9) B)) ∧
      ∃ (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
        (hib : ∀ y, ‖f.inputMask y‖ ≤ 1),
      let retarded := fun o : Fin 2 ↦ (sourceCutMultiplier output ho hob).comp
        ((finitePhysicalOperator (fun p ↦ (f.chart p).index) (Op o)).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
      let W₁ := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p) 1
      let T := fun o : Fin 2 ↦ if o = 0 then
        selectedFiniteDirectSolver f L Q B output ho hob (retarded 0) else
        selectedFiniteDirectResidual f L Q B W₁ output ho hob (retarded 1)
      let Tplus := fun o : Fin 2 ↦ (1/2 : ℂ) • (T o +
        (sourceCutMultiplier output ho hob).comp
          (if o = 0 then ellipticSolver f hout L Q else ellipticResidual f hout L Q B))
      ((((∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (T 0 u y).ofLp) φ j = ∫ y, φ y •
            ((1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1)) u) y j) ∧
      (∀ (u : H) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (pairedSolver f hout L Q B output ho hob (retarded 0) u y).ofLp) φ j =
          ∫ y, φ y • (pairedSource f hout L output ho hob +
            pairedResidual f hout L Q B output ho hob W₁ (retarded 1)) u y j) ∧
      (∀ (u : Lp (EuclideanSpace ℝ (Fin (d+1))) 2 (volume : Measure E)) (φ : E → ℝ),
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball x r → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (l2ComplexInclusion volume
            (realSolver f hout L Q B output ho hob (retarded 0) u) y).ofLp) φ j =
          ∫ y, φ y • l2ComplexInclusion volume
            ((realSource f hout L output ho hob +
              realResidual f hout L Q B output ho hob W₁ (retarded 1)) u) y j) ∧
      (∀ (o : Fin 2) (s : ℕ) (V : H →L[ℂ] H),
        (V = Tplus o ∨ V = (Tplus o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
        vectorFourierSobolevNorm (s : ℝ) (V u) ≤ completeCost o s *
          (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u +
            (1+cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (s-o.val+sectorLowOrder d) B)*‖u‖)) ∧
      (∀ (o : Fin 2) (k : ℕ) (V : H →L[ℂ] H),
        (V = Tplus o ∨ V = (Tplus o).adjoint) → ∀ u,
        MemVectorFourierSobolev (-(k : ℝ)) (V u) ∧
        vectorFourierSobolevNorm (-(k : ℝ)) (V u) ≤
          ((d+1 : ℝ)*(d+1)*completeCost o (k+o.val)) *
            (2+cNorm (closedBall x RQ) (k+sectorLowOrder d) Q+
              cNorm (closedBall x RQ) (k+sectorLowOrder d) B) *
            vectorFourierSobolevNorm (-((k+o.val : ℕ) : ℝ)) u) ∧
      ∀ (U V : Set E) (hU : MeasurableSet U), MeasurableSet V →
        (∀ u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev V 1 (localRetardedOperator hU V (Tplus 1) u) ∧
          restrictionSobolevNorm V 1 (localRetardedOperator hU V (Tplus 1) u) ≤
            completeLocalCost*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℂ (Fin (d+1))),
          MemRestrictionSobolev U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ∧
          restrictionSobolevNorm U 1 ((localRetardedOperator hU V (Tplus 1)).adjoint v) ≤
            completeLocalCost*‖v‖) ∧
        let R := localRealCompression hU V
          (pairedResidual f hout L Q B output ho hob W₁ (retarded 1))
        (∀ u : LocalL2 U (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev V 1 (R u) ∧ restrictionSobolevNorm V 1 (R u) ≤
            (4*completeLocalCost)*‖u‖) ∧
        (∀ v : LocalL2 V (EuclideanSpace ℝ (Fin (d+1))),
          MemRestrictionSobolev U 1 (R.adjoint v) ∧ restrictionSobolevNorm U 1 (R.adjoint v) ≤
            (4*completeLocalCost)*‖v‖)) ∧
      ∃ S : Fin 2 → graphTestSpace (d+1) (d+1) →ₗ[ℂ] (E → CF),
      ∃ A : graphTestSpace (d+1) (d+1) →ₗ[ℂ] (E → CF),
      ∃ SR : Fin 2 → realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF),
      ∃ AR : realSectorTestSpace d (d+1) →ₗ[ℝ] (E → RF),
      (∀ o u, ContDiff ℝ ∞ (S o u) ∧ S o u =ᵐ[volume]
        (if o = 0 then pairedSolver f hout L Q B output ho hob (retarded 0)
          else pairedResidual f hout L Q B output ho hob W₁ (retarded 1)) (graphTestToLp u)) ∧
      (∀ u, ContDiff ℝ ∞ (A u) ∧ A u =ᵐ[volume]
        pairedSource f hout L output ho hob (graphTestToLp u)) ∧
      (∀ o u, ContDiff ℝ ∞ (SR o u) ∧ SR o u =ᵐ[volume]
        (if o = 0 then realSolver f hout L Q B output ho hob (retarded 0)
          else realResidual f hout L Q B output ho hob W₁ (retarded 1)) (realSectorTestToLp u) ∧
        (fun y ↦ euclideanComplexInclusion (SR o u y)) = S o (realSectorTestInclusion u)) ∧
      (∀ u, ContDiff ℝ ∞ (AR u) ∧ AR u =ᵐ[volume]
        realSource f hout L output ho hob (realSectorTestToLp u) ∧
        (fun y ↦ euclideanComplexInclusion (AR u y)) = A (realSectorTestInclusion u)) ∧
      (∀ u, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (S 0 u y).ofLp) (fderiv ℝ (fun y ↦ (S 0 u y).ofLp)))
        (fun y ↦ (A u y + S 1 u y).ofLp) (ball x r)) ∧
      (∀ u, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (euclideanComplexInclusion (SR 0 u y)).ofLp)
        (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (SR 0 u y)).ofLp)))
        (fun y ↦ (euclideanComplexInclusion (AR u y + SR 1 u y)).ofLp) (ball x r))) ∧
      (∀ u : graphTestSpace (d+1) (d+1),
        ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
          Mollification.HasWeakFDerivOn volume
            (fun y ↦ (pairedSolver f hout L Q B output ho hob (retarded 0) (graphTestToLp u) y).ofLp)
            D univ ∧ MemLp D 2 volume ∧
          physicalWeakApply
            (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
            (fun y ↦ (pairedSolver f hout L Q B output ho hob (retarded 0) (graphTestToLp u) y).ofLp)
            D =ᵐ[volume.restrict (ball x r)]
            fun y ↦ ((pairedSource f hout L output ho hob +
              pairedResidual f hout L Q B output ho hob W₁ (retarded 1)) (graphTestToLp u) y).ofLp) ∧
      (∀ u : realSectorTestSpace d (d+1),
        ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
          Mollification.HasWeakFDerivOn volume
            (fun y ↦ (l2ComplexInclusion volume
              (realSolver f hout L Q B output ho hob (retarded 0) (realSectorTestToLp u)) y).ofLp)
            D univ ∧ MemLp D 2 volume ∧
          physicalWeakApply
            (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
            (fun y ↦ (l2ComplexInclusion volume
              (realSolver f hout L Q B output ho hob (retarded 0) (realSectorTestToLp u)) y).ofLp)
            D =ᵐ[volume.restrict (ball x r)]
            fun y ↦ (l2ComplexInclusion volume
              ((realSource f hout L output ho hob +
                realResidual f hout L Q B output ho hob W₁ (retarded 1)) (realSectorTestToLp u)) y).ofLp)) ∧
      let U := ball x (min r f.physicalRadius)
      let normDomain := ball x normRadius
      let R := localRealCompression (U := normDomain) isOpen_ball.measurableSet U
        (pairedResidual f hout L Q B output ho hob W₁ (retarded 1))
      ∃ hmem : ∀ u, MemRestrictionSobolev U 1 (R u),
      ∃ hbound : ∀ u, restrictionSobolevNorm U 1 (R u) ≤
          (4*completeLocalCost)*‖u‖,
      let Rp := residualToLpOnBall x hrU hUW R hmem hbudget hbound
      let Kloc := localizedResidual (two_lt_ballSobolevExponent x hrU).le
        χ₂ χ₃ isOpen_ball.measurableSet Rp
      let Inv := neumannInverse Kloc
      let Corr := correctedSource (two_lt_ballSobolevExponent x hrU).le
        χ₂ χ₃ isOpen_ball.measurableSet Rp
      let uQ := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall Q hQ.contDiffOn
      let uB := smoothCoefficientL2 hΩ (hRQ.trans hQR) hNormBall B hB.contDiffOn
      let a := fun s ↦ restrictionSobolevNorm normDomain s uQ + restrictionSobolevNorm normDomain s uB
      let β := sectorLowOrder d + (d+2)
      ‖Kloc‖ ≤ κ ∧ HasSum (fun j : ℕ ↦ (-Kloc)^j) Inv ∧
      (1+Kloc)*Inv = 1 ∧ Inv*(1+Kloc) = 1 ∧ ‖Inv‖ ≤ (1-κ)⁻¹ ∧
      (∀ u : LocalL2 normDomain E, Kloc u =ᵐ[volume.restrict normDomain]
        zeroExtend isOpen_ball.measurableSet
          (bumpL2 (p := 2) le_rfl χ₂ (R (bumpL2 (p := 2) le_rfl χ₃ u)))) ∧
      (∀ (s : ℕ) (u : LocalL2 normDomain E), MemRestrictionSobolev normDomain s u →
        (MemRestrictionSobolev normDomain (s+1) (Kloc u) ∧
          restrictionSobolevNorm normDomain (s+1) (Kloc u) ≤ gainCost (s+1) *
            (restrictionSobolevNorm normDomain s u + (1+a (s+1+β))*‖u‖)) ∧
        (MemRestrictionSobolev normDomain (s+1) (Kloc.adjoint u) ∧
          restrictionSobolevNorm normDomain (s+1) (Kloc.adjoint u) ≤ gainCost (s+1) *
            (restrictionSobolevNorm normDomain s u + (1+a (s+1+β))*‖u‖))) ∧
      (∀ (s : ℕ) (u : LocalL2 normDomain E), MemRestrictionSobolev normDomain s u →
        MemRestrictionSobolev normDomain s (Inv u) ∧
          restrictionSobolevNorm normDomain s (Inv u) ≤ inverseTameConstant κ gainCost s *
            (restrictionSobolevNorm normDomain s u + (1+a (s+β))*‖u‖)) ∧
      (∀ (s : ℕ) (u : LocalL2 normDomain E), MemRestrictionSobolev normDomain s u →
        MemRestrictionSobolev normDomain s (Corr u) ∧
          restrictionSobolevNorm normDomain s (Corr u) ≤ correctionCost s *
            (restrictionSobolevNorm normDomain s u + (1+a (s+β))*‖u‖)) ∧
      (∀ (s : ℕ) (u : LocalL2 normDomain E), MemRestrictionSobolev normDomain s u → ∀ V : Set E,
        let Su := localRealCompression isOpen_ball.measurableSet V
          (pairedSolver f hout L Q B output ho hob (retarded 0)) (Corr u)
        MemRestrictionSobolev V s Su ∧ restrictionSobolevNorm V s Su ≤ responseCost s *
          (restrictionSobolevNorm normDomain s u + (1+a (s+β))*‖u‖)) ∧
      (∀ h : smoothSource normDomain E, ∃ v : E → E,
        ContDiffOn ℝ ∞ v normDomain ∧ v =ᵐ[volume.restrict normDomain] Inv h) ∧
      (∃ Zsmooth : smoothSource normDomain E →ₗ[ℝ] (E → E), ∀ h,
        ContDiff ℝ ∞ (Zsmooth h) ∧ Zsmooth h =ᵐ[volume.restrict normDomain] Corr h ∧
        tsupport (Zsmooth h) ⊆ tsupport (χ₂ : E → ℝ) ∧
        normDomain.indicator (Zsmooth h) = Zsmooth h ∧
        Zsmooth h =ᵐ[volume] zeroExtend isOpen_ball.measurableSet (Corr h) ∧
        ∀ y, χ₃ y • Zsmooth h y = Zsmooth h y) ∧
      (∀ h : LocalL2 normDomain E,
        (∀ᵐ y ∂volume.restrict normDomain, y ∉ tsupport (χ₂ : E → ℝ) → Corr h y = 0) ∧
        bumpL2 (p := 2) le_rfl χ₃ (Corr h) = Corr h ∧
        (∀ᵐ y ∂volume.restrict (ball x χ₂.rIn), Corr h y + R (Corr h) y = h y) ∧
        (∀ᵐ y ∂volume, y ∉ tsupport (χ₂ : E → ℝ) →
          zeroExtend isOpen_ball.measurableSet (Corr h) y = 0) ∧
        ‖Corr h‖ ≤ (1-κ)⁻¹*‖h‖) ∧
      (∀ (h : LocalL2 normDomain E) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball x χ₂.rIn → ∀ j,
        physicalTestAction
          (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
          (fun y ↦ (l2ComplexInclusion volume
            (realSolver f hout L Q B output ho hob (retarded 0)
              (zeroExtend isOpen_ball.measurableSet (Corr h))) y).ofLp) φ j =
        ∫ y, φ y • l2ComplexInclusion volume
          (zeroExtend isOpen_ball.measurableSet h +
            realSource f hout L output ho hob
                (zeroExtend isOpen_ball.measurableSet (Corr h)) -
            zeroExtend isOpen_ball.measurableSet (Corr h)) y j) ∧
      ∃ smoothSolver smoothRight : smoothSource normDomain E →ₗ[ℝ] (E → E),
        (∀ h : smoothSource normDomain E,
          ContDiff ℝ ∞ (smoothSolver h) ∧
          smoothSolver h =ᵐ[volume] realSolver f hout L Q B output ho hob (retarded 0)
              (zeroExtend isOpen_ball.measurableSet (Corr h))) ∧
        (∀ h : smoothSource normDomain E,
          ContDiff ℝ ∞ (smoothRight h) ∧
          smoothRight h =ᵐ[volume] (realSource f hout L output ho hob +
            realResidual f hout L Q B output ho hob W₁ (retarded 1))
                (zeroExtend isOpen_ball.measurableSet (Corr h))) ∧
        (∀ h : smoothSource normDomain E,
          smoothRight h =ᵐ[volume.restrict (ball x χ₂.rIn)]
            (zeroExtend isOpen_ball.measurableSet (h : LocalL2 normDomain E) +
              realSource f hout L output ho hob
                  (zeroExtend isOpen_ball.measurableSet (Corr h)) -
              zeroExtend isOpen_ball.measurableSet (Corr h))) ∧
        (∀ (h : smoothSource normDomain E) (m : ℕ) (Rout : ℝ), 0 < Rout → Rout < normRadius →
          cNorm (closedBall x Rout) m (smoothSolver h) ≤
            (classicalCost m * responseCost (m + (d+2))) *
              (restrictionSobolevNorm normDomain (m + (d+2)) (h : LocalL2 normDomain E) +
                (1+a (m+(d+2)+β))*‖(h : LocalL2 normDomain E)‖)) ∧
        (∀ (Lsource : ℂ →L[ℝ] E) (m : ℕ) (Rout : ℝ),
          0 < Rout → Rout < normRadius →
          ∀ (h : RetardedSobolev.Spaces.Test d) (y : E), y ∈ closedBall x Rout →
            ‖iteratedFDeriv ℝ m (smoothSolver (retardedTestSmoothSource normDomain Lsource h)) y‖ ≤
              (((classicalCost m * responseCost (m+(d+2))) * (2+a (m+(d+2)+β))) *
                (‖Lsource‖ * sourceJetCost (m+(d+2)))) *
                  ‖RetardedSobolev.Spaces.ofTest (m+(d+2)) volume h‖) ∧
        ∀ h : smoothSource normDomain E,
          EqOn (physicalWeakApply
            (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
            (fun y ↦ (euclideanComplexInclusion (smoothSolver h y)).ofLp)
            (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (smoothSolver h y)).ofLp)))
            (fun y ↦ (euclideanComplexInclusion (smoothRight h y)).ofLp) (ball x χ₂.rIn) := by
  classical
  obtain ⟨M, hM, hAd⟩ := PhysicalInitialization.exists_terminal_physical_admission_on_source_dilation
    ext hext heb hbR m hm
  obtain ⟨aperture, hAp, hApξ, θ, hθ, hbuffer, f, hsourcePlateau, hcollar,
    sourceMargin, hmargin, τ, hτ, hstationary⟩ :=
    exists_signed_terminal_envelope_family_of_coefficient_cap P T hframe Csrc hCsrc hcsrc Xsrc hXsrc
      hsource hΩ x hRQ hKΩ hKprimary hd hin hout hnest hsym hbad hgap (radius := radius) hM.le
  obtain ⟨η, hη, hadmission⟩ := hAd f Unit inferInstance (fun _ ↦ sourceMargin) (fun _ ↦ hmargin) ηprotect hprotect
  refine ⟨M, hM, aperture, hAp, hApξ, θ, hθ, hbuffer, f, hsourcePlateau, hcollar,
    sourceMargin, hmargin, τ, hτ, hstationary, η, hη, ?_⟩
  have hinverse := exists_normalized_complete_smooth_fixed_inverse_of_selected_collar
    hΩ x hRQ hKΩ (cubeStress (d+1)) hout hM.le f hcollar hκ₀ hκ₁
  choose evolutionTime speedGap rootSize rootCost hprotection hcommon
    hradii hevolution hlocal hfixed using hinverse
  refine ⟨evolutionTime, speedGap, rootSize, rootCost, hprotection, hcommon,
    hradii, hevolution, hlocal, ?_⟩
  choose L hL angular χout χsource hs output r hr ho horange hoc hos
    hop hsourceMask houtMask hselected hthreshold hconstants using hfixed
  refine ⟨L, hL, angular, χout, χsource, hs, output, r, hr, ho, horange, hoc, hos,
    hop, hsourceMask, houtMask, hselected, hthreshold, ?_⟩
  choose base cost maskCost Rbox Dpdo Dgain Gain ra rb amplitudeCost
    hbase hcost hmaskCost hRbox hDpdo hDgain hGain hra hrab hamp
    hangular hcoverage completeCost hcompleteCost completeLocalCost hcompleteLocalCost
    normRadius hQR hNormBall coefficientCost hcoefficientCost hcoefficientBounds
    hbudget hrU hUW χ₂ χ₃ h₂ h₃ hnestχ hne hopen hcore hplateau hmaskPlateau
    gainCost hgainCost correctionCost responseCost classicalCost
    hcorrectionCost hresponseCost hclassicalCost sourceJetCost hsourceJetCost
    hoperators using hconstants
  refine ⟨base, cost, maskCost, Rbox, Dpdo, Dgain, Gain, ra, rb, amplitudeCost,
    hbase, hcost, hmaskCost, hRbox, hDpdo, hDgain, hGain, hra, hrab, hamp, hangular, hcoverage,
    completeCost, hcompleteCost, completeLocalCost, hcompleteLocalCost,
    normRadius, hQR, hNormBall, coefficientCost, hcoefficientCost, hcoefficientBounds,
    hbudget, hrU, hUW, χ₂, χ₃, h₂, h₃, hnestχ, hne, hopen, hcore, hplateau,
    hmaskPlateau, gainCost, hgainCost, correctionCost, responseCost, classicalCost,
    hcorrectionCost, hresponseCost, hclassicalCost, sourceJetCost, hsourceJetCost, ?_⟩
  obtain ⟨_, _, _, contractionCap, hpositive, hbelow, hone, _, hsmall, _⟩ :=
    ReferenceInitialization.FullCoefficientDilation.exists_fullReducedCoefficients_finite_margin_interval G₀
        (isCompact_closedBall (0 : E) b) ({()} : Finset Unit)
        (fun _ ↦ max m (sectorLowOrder d)) (fun _ ↦ η)
        (by intro i hi; exact hη) (ε₆ := 1) zero_lt_one hsourceCap
  refine ⟨contractionCap, hpositive, hbelow, hone, ?_⟩
  intro ρ hρ Gref hsame
  have href : cNorm (closedBall (0 : E) b) (max m (sectorLowOrder d))
      (geometricReducedCoefficients Gref.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < η := by
    rw [hsame]
    exact (hsmall ρ hρ).2.2.2.2.1 () (Finset.mem_singleton_self ())
  have hadmitted := hadmission G₀ Gref ρ hρ.1 (hρ.2.trans hone) hsame hR href
  refine ⟨hadmitted.1, ?_⟩
  intro Cband hband rStar kMin hStar hreserve horder
  obtain ⟨S, hS, hhistory⟩ := hadmitted.2 hband rStar kMin hStar hreserve horder
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu F Q B
  obtain ⟨hQ, hB, hrange, hphase, hcap⟩ := hhistory R₀ hR₀ s u ell hu
  have hlow := hcap (closedBall x RQ) (isCompact_closedBall _ _)
  exact ⟨hQ, hB, hrange, hphase (), hcap,
    hoperators Q hQ.contDiffOn (hrange.mono_left (subset_univ _)) hlow.1
      B hB.contDiffOn hlow.2.1⟩

end JanetCartan.FixedDomainInverse
