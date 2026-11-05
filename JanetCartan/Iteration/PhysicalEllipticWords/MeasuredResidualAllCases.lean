module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedLetters
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicLetters
public import JanetCartan.Iteration.PhysicalPrimary.EllipticLetter

/-!
# Every actual measured letter of the complete residual

Apply all four original analytic constructors on one physical history, full
coefficient family, phase, source and measured alphabet. The only finite
threshold is chosen before the physical family/history. No letter estimate,
polynomial response cost, or finite-word estimate is an input.

Consumer: `FiniteResidualWordProfiles.actual_finite_residual_word_reserved_bounds_of_one_step.hstep`
(`app:ch_regular:lem:finite-chain`, `app:ch_response:eq:response-graded-reduced`).
The original-data realization of the primitive chart/coefficient certificates
remains with the physical-primary parent; the final solver is a separate input
producer, not assumed here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap JanetCartan.RegularSector.Realization

namespace JanetCartan.PhysicalEllipticWords
open FixedDomainInverse FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer RetainedCharacteristicEnvelopes
open FullSourceEnvelopes RegularSector.Characteristic.ResidualCoordinates
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral AmplitudeBounds SymbolBudgets
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open ResponseTransfer.Complement UniformEvolution IntegratedEnvelope RegularSector.FiniteMasks
open RetainedFactors WholeImageGeometry FullSourceStationary
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open RegularSector.FiniteAssembly RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ConicAmplitude
open PhysicalPrimary CharacteristicPartition ParameterSourceCutoffs FiniteResidualWordProfiles
open FixedDomainInverse.FiniteResidualEnvelopes RegularSector.NormalizedSolver
open ArbitraryAccuracy.SelectedLocalization RegularSector.FiniteEvolution
open RegularSector.FiniteResidual.FiniteIdentity
open CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.PdoRealization

variable {d : ℕ} {I ι : Type} [Fintype ι]
variable {P : Patch (d+1)} {Uref : Set (Euclidean (d+1))} {hUref : IsOpen Uref}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => Lp F 2 (volume : Measure E)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ Mcap : ℝ}
  {K₀ : Set (Euclidean (d+1))}

/-- All four literal letters, with the unchanged natural parameter/spatial
reserve. The source support is exactly the output measurement support, as
required by the complete residual-power induction. Thresholds precede `R₀`,
all physical prefixes, and the actual coefficient/operator families. -/
theorem exists_physical_history_measured_residual_alphabet_bounds
    (T : PatchQuantitativeFamily P Uref hUref)
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap)
    (χp : f.centers → E × Par → ℝ) (hcχp : ∀ p, HasCompactSupport (χp p))
    (evolutionTime speedGap rootSize : f.centers → ℝ) (rootCost : f.centers → ℕ → ℝ)
    (hprotect : ∀ p, LocalProtectionCertificate (f.chart p)
      (evolutionTime p) (speedGap p) (rootSize p) (rootCost p))
    (hbufferTarget : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcBuffer : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ε aperture timeRadius : f.centers → ℝ) (g Rad : f.centers → Bool → ℝ)
    (hε : ∀ p, 0 < ε p) (hεroot : ∀ p, ε p ≤ (f.chart p).rootRadius)
    (hεbuffer : ∀ p, ε p ≤ (f.chart p).bufferRadius/8)
    (hAp : ∀ p, 0 < aperture p) (hg : ∀ p negative, 0 < g p negative)
    (hRad : ∀ p negative, 0 < Rad p negative)
    (htime : ∀ p, 0 < timeRadius p) (htimeε : ∀ p, timeRadius p ≤ ε p)
    (hsrctime : ∀ p, (f.chart p).maskRadius ≤ timeRadius p)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    (V : f.centers → Bool → Set Par) (hV : ∀ p negative, IsOpen (V p negative))
    (hVc : ∀ p negative, IsCompact (closure (V p negative)))
    (hVcov : ∀ p negative, ∀ q ∈ closure (V p negative),
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Vwhole Csrc : Set Par} (hVwhole : IsOpen Vwhole)
    (hVwholec : IsCompact (closure Vwhole))
    (hVwholecov : ∀ q ∈ closure Vwhole,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hCsrc : IsClosed Csrc) (hCsrcV : Csrc ⊆ Vwhole)
    (χinc : f.centers → Bool → Par → ℝ)
    (hχinc : ∀ p negative, ContDiff ℝ ∞ (χinc p negative))
    (hcχinc : ∀ p negative, HasCompactSupport (χinc p negative))
    (hsχinc : ∀ p negative, tsupport (χinc p negative) ⊆ V p negative)
    (aWhole BWhole : f.centers → ℝ) (haWhole : ∀ p, 0 < aWhole p)
    (gapInactive : f.centers → Bool → ℝ)
    (hgapInactive : ∀ p negative, 0 < gapInactive p negative)
    (a₀ B₀ : f.centers → Bool → ℝ) (m Mfreq : f.centers → ℝ)
    (ha₀ : ∀ p negative, 0 < a₀ p negative) (hB₀ : ∀ p negative, 0 < B₀ p negative)
    (hm : ∀ p, 0 < m p) (hm1 : ∀ p, m p ≤ 1) (hMfreq : ∀ p, 1 ≤ Mfreq p)
    (InvBound : f.centers → Bool → ℝ) (hInv : ∀ p negative, 0 ≤ InvBound p negative)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : f.centers → Euclidean d → ℝ) (hang : ∀ p, ContDiff ℝ ∞ (angular p))
    (hangPlateau : ∀ p, ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask (angular p) =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (Damp : f.centers → ℕ → ℝ) (hDamp : ∀ p j, 0 ≤ Damp p j)
    (ra rb : f.centers → ℝ)
    (rectOut rectSource : f.centers → E → ℂ)
    (hrectSource : ∀ p, ContDiff ℝ ∞ (rectSource p))
    (base : f.centers → Fin 2 → ℝ) (cost : f.centers → Fin 2 → ℕ → ℝ)
    (hlocalout : ∀ p y, (output y : ℂ)*rectOut p ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ))
    (hlocalin : ∀ p y, rectSource p ((physicalCoordinates (f.chart p).index).symm y)*(f.inputMask y : ℂ) =
      (f.inputMask y : ℂ))
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Bband : ℝ} (hBband : 1 ≤ Bband)
    {rStar Rstar kMin Rsource : ℕ} (hStar : 8 ≤ rStar)
    (hRstar : fullLowReserve (d+1)+2 < Rstar)
    (hcompression : Rsource + fullLowReserve (d+1) + 4 ≤ Rstar) (hreserve : Rstar+10 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin)
    (basis : OrthonormalBasis ι ℝ CW) {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    let c := fun p ↦ f.chart p
    let z := fun p ↦ ((coordinateSplit (c p).index x).1,
      ((coordinateSplit (c p).index x).2,(coordinateSplit (c p).index p.val.val).2))
    let U := fun p ↦ elapsedPhysicalBox (z p) (ε p/2)
    let O := fun p negative ↦ retainedOpenAnnularFrequencyCarrier (c p).radialSection (z p).2.2
      (ε p/2) (aperture p) (g p negative) (Rad p negative)
    let D := fun p negative ↦ retainedOpenIntegrationDomain (z p) (ε p) (O p negative)
    let Z := fun p negative ↦ Ioo (-2*timeRadius p) (2*timeRadius p) ×ˢ (U p ×ˢ V p negative)
    let KP := fun p negative ↦ closure (elapsedPhysicalBox (z p) (ε p)) ×ˢ closure (V p negative)
    let KPwhole := fun p ↦ closure (elapsedPhysicalBox (z p) (ε p)) ×ˢ closure Vwhole
    let PInactive := fun p negative ↦ Csrc ∩ tsupport (fun b ↦ 1-χinc p negative b)
    let Ksigned := fun p negative ↦ fullSourceSignedCarrier (z p) (ε p)
      (closure (V p negative)) (O p negative)
    let β := fun p ↦ selectedEndpointMultiplier f p threshold
    (∀ p, MapsTo (primaryCoordinateChange (c p).index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (U p)) →
    (∀ p, tsupport (f.angularMask p ∘ physicalCoordinates (c p).index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone (c p).radialSection (z p).2.2 (ε p/4) (aperture p/2)) →
    (∀ p negative, retainedAnnularFrequencyCarrier (c p).radialSection (z p).2.2
      (ε p/2) (aperture p)
      (retainedSelectorGap (z p).2.2 (ε p/2) (aperture p) (a₀ p negative/(2*Mfreq p)))
      (2*(2*B₀ p negative/m p)) ⊆ O p negative) →
    (∀ p, RetainedConstruction.DiagonalFrequencyCoverage (c p).radialSection (z p).2.2
      ((c p).bufferRadius/2) (ra p) (rb p) (β p)) →
    (∀ p y, endpointOutputMask f p output y ≠ 0 → (c p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) →
    (∀ p negative, ∀ q ∈ KP p negative, χp p =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    (∀ p, ∀ q ∈ KPwhole p, χp p =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧
    ∀ (R₀ : I → ℝ) (n : I → ℕ)
      (u : ∀ i, Fin (n i) → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
      (ell : ∀ i, Fin (n i) → ℕ), (∀ i, S₀ ≤ R₀ i) →
      (∀ i, RevisedGlobal.IsAdmissibleHistory Bband (R₀ i) kMin (u i) (ell i)) →
    ∀ Q : I → {Q : E → Coeff // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold},
      (∀ i, (Q i).1 = extendedProjectedStress ext (RevisedGlobal.finiteMap Gref.map (u i))) →
    let B := fun i ↦ reducedZerothProjection (d+1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (RevisedGlobal.finiteMap Gref.map (u i))
    let L := fun i ↦ currentCoefficientScale (R₀ i) (n i)
    let sourcePhase := fun p negative i ↦ if negative then
      T.negativeFullSourcePhaseInCoordinates (c p).index (Q i)
      else T.fullSourcePhaseInCoordinates (c p).index (Q i)
    ∀ (h : f.centers → I → RootState (Euclidean d) → ℝ)
      (Φ : f.centers → I → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (chart : f.centers → I → OpenPartialHomeomorph TC TC) (G : f.centers → I → TC → ℝ),
      (∀ p i, closedBall ((z p).1,z p) (c p).targetRadius ⊆ (chart p i).target) →
      (∀ p i, ContDiffOn ℝ ∞ (twoTimePhase (chart p i)) (chart p i).target) →
      (∀ p i q, q ∈ (chart p i).target → HasFDerivAt (twoTimePhase (chart p i))
        (twoTimePhaseDifferential (h p i) (Φ p i) (chart p i) q) q) →
      (∀ p i q, q ∈ closedBall ((z p).1,z p) (c p).targetRadius →
        ‖twoTimePhaseMixed (chart p i) q - 1‖ ≤ 1/2) →
      (∀ p i j, cNorm (closedBall ((z p).1,z p) (c p).targetRadius) j (twoTimePhase (chart p i)) ≤
        (c p).phaseCost j * (1+cNorm (closedBall x RQ) (j+1) (Q i).1)) →
      (∀ p i q, q ∈ (chart p i).target → ((chart p i).symm q).2.1 = q.2.1) →
    let Fs := fun p i ↦ selectedBufferedAmplitude f p (Q i).1 (B i) (Φ p i) (chart p i)
    let matrix := fun p i k ↦ collared (c p).radialSection (if k=0 then 0 else 1)
      (angular p) (Fs p i k)
    let Ws := fun p i ↦ selectedConicAmplitude f p (Q i).1 (B i) (Φ p i) (chart p i) (angular p)
    (∀ p i k, ContDiff ℝ ∞ (Fs p i k)) → (∀ p i k, ContDiff ℝ ∞ (matrix p i k)) →
    (∀ p i k, tsupport (matrix p i k) ⊆ ConicPhase.domain (c p).radialSection
      ((chart p i).target ∩ (chart p i).symm ⁻¹'
        (ball (z p).1 ((c p).maskRadius/2) ×ˢ
          (ball (z p).1 ((c p).maskRadius/2) ×ˢ ball (z p).2 ((c p).maskRadius/2))))) →
    (∀ p i q, q ∈ tsupport (matrix p i 0) ∪ tsupport (matrix p i 1) →
      G p i =ᶠ[𝓝 q] phase (c p).radialSection (chart p i)) →
    (∀ p i q, (c p).timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → matrix p i 2 q ≠ 0 →
      G p i =ᶠ[𝓝 q] phase (c p).radialSection (chart p i)) →
    (∀ p i k j, BoundedTwoTimeOrderSeminorm (if k=0 then 0 else 1)
      (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (Ws p i k) ∧
      twoTimeOrderSeminorm (if k=0 then 0 else 1)
        (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (Ws p i k) ≤
        Damp p j * (1+cNorm (closedBall x RQ) (j+10) (Q i).1+cNorm (closedBall x RQ) (j+9) (B i))) →
    (∀ p negative i q, q ∈ KP p negative →
      a₀ p negative ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ≤ B₀ p negative) →
    (∀ p i q, q ∈ KPwhole p →
      aWhole p ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates (c p).index (Q i) y q.2) q.1‖ ≤ BWhole p) →
    (∀ p i t, t ∈ Icc 0 (ε p) → ∀ y ∈ U p,
      ∀ ξ ∈ retainedFrequencyDomain (c p).radialSection (z p) (ε p) (aperture p) (1/2),
        m p*‖ξ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase (c p).radialSection (chart p i)) t v ξ) y‖ ∧
        ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase (c p).radialSection (chart p i)) t v ξ) y‖ ≤ Mfreq p*‖ξ‖) →
    ∀ Op : f.centers → I → Fin 2 → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
      (∀ p i o, RetainedSignedRetardedBounds (closedBall x RQ) (Q i).1 (B i) (3*(c p).maskRadius/4)
        ((z p).1-(c p).maskRadius/2) (fun t s y ξ ↦ G p i (t,(s,(y,ξ))))
        (if o=0 then Ws p i 0+Ws p i 1 else Ws p i 2) (rectOut p) (rectSource p) (β p)
        (hrectSource p) o.val (base p o) (cost p o) (Op p i o)) →
    ∀ κ : f.centers → Bool → I → (ℝ × (E × Par)) → CW,
    let raw := fun p negative i ↦ fullSourceJointPhase false
      (curriedPhase (c p).radialSection (chart p i)) (sourcePhase p negative i)
    (∀ p negative i, ContDiffOn ℝ ∞ (raw p negative i) (Z p negative ×ˢ D p negative)) →
    (∀ p negative i, ContDiffOn ℝ ∞ (κ p negative i) (Z p negative)) →
    (∀ p negative i q, q ∈ Z p negative → κ p negative i q ∈ D p negative ∧
      gradient (fun w ↦ raw p negative i (q,w)) (κ p negative i q) = 0 ∧
      raw p negative i (q,κ p negative i q) = 0) →
    (∀ p negative i q, q ∈ Z p negative → ∀ w ∈ closure (D p negative),
      let phase := fun b w ↦ raw p negative i ((q.1,b),w)
      IsUnit (averagedPhaseHessian phase (fun b ↦ κ p negative i (q.1,b)) q.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian phase (fun b ↦ κ p negative i (q.1,b)) q.2 w)‖ ≤
          InvBound p negative) →
    (∀ p negative i q, q ∈ Z p negative → ∀ w ∈ closure (D p negative),
      ∀ t ∈ uIcc (0 : ℝ) q.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((t,q.2),κ p negative i q + a • (w-κ p negative i q)) ∈ Ksigned p negative) →
    (∀ p negative i b, b ∈ Vwhole → b ∈ PInactive p negative →
      ∀ t ∈ Icc 0 (3*(c p).maskRadius/4), ∀ y ∈ U p, ∀ ξ ∈ tsupport (β p),
      gapInactive p negative ≤
        dist (NormedSpace.normalize (gradient (fun y ↦ sourcePhase p negative i y b) y))
          (NormedSpace.normalize ξ)) →
    ∀ (lam K Adata : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ Adata i) →
    ∀ (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i))),
      (∀ p i b y, φ i (physicalCoordinates (c p).index y) b = χp p (y,b)*sourcePhase p false i y b) →
    ∀ (χout χin : E → ℝ) (hχout : ContDiff ℝ ∞ χout) (hcχout : HasCompactSupport χout)
      (hχin : Continuous χin) (hbχout : ∀ y, ‖χout y‖ ≤ 1) (hbχin : ∀ y, ‖χin y‖ ≤ 1),
      (∀ y ∈ tsupport χout, χin y = 1) →
      (∀ p, physicalCoordinates (c p).index ⁻¹' tsupport χout ⊆ U p) →
      (tsupport χout ⊆ ball x (3*f.physicalRadius)) →
    ∀ (hK₀ : IsCompact K₀) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
      (W₁ : I → f.centers → TwoTimeAmplitude d (d+1))
      (retarded : I → f.centers → H →L[ℂ] H), (∀ p i, retarded i p = Op p i 1) →
    (hΩ : IsOpen Ω) → (hRQ : 0 ≤ RQ) → (hball : closedBall x RQ ⊆ Ω) →
    (hft : f.radialThreshold ≤ threshold) →
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col (cubeStress (d+1)) p.val.val c.root
        c.coefficientRadius c.rootRadius c.minorGap c.transportGap) →
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall (cubeStress (d+1)) f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
          complementDomain c.index (fun _ : E ↦ A')
            (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root)
            c.row c.col (normalizedRootDomain c)) →
    ∀ (AQ AB Aphase Dendpoint Dalgebraic : ℕ → ℝ) (Wcost : f.centers → ℕ → ℝ),
      (∀ j, 0 ≤ AQ j) → (∀ j, 0 ≤ AB j) → (∀ j, 0 ≤ Aphase j) →
      (∀ j, 0 ≤ Dendpoint j) → (∀ j, 0 ≤ Dalgebraic j) → (∀ p j, 0 ≤ Wcost p j) →
      (∀ i, ContDiffOn ℝ ∞ (Q i).1 Ω) → (∀ i, ContDiffOn ℝ ∞ (B i) Ω) →
      (∀ i, MapsTo (Q i).1 Ω (closedBall (cubeStress (d+1)) f.coefficientRadius)) →
      (∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i).1 ≤ Mcap) →
      (∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ Mcap) →
      (∀ i j, cNorm (closedBall x RQ) j (Q i).1 ≤ AQ j * L i^(j-rStar)) →
      (∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i^(j-rStar)) →
      (∀ i p, ContDiff ℝ ∞ (jointAmplitude (W₁ i p))) →
      (∀ i p j, BoundedTwoTimeOrderSeminorm 1
        (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (W₁ i p) ∧
        twoTimeOrderSeminorm 1
          (bufferedJetSet (c p).radialSection (z p) ((c p).bufferRadius/2) (ra p) (rb p)) j (W₁ i p) ≤
          Wcost p j * (1+cNorm (closedBall x RQ) (j+10) (Q i).1+cNorm (closedBall x RQ) (j+9) (B i))) →
    ∀ (Rnormal : f.centers → I → ℝ) (Dgain Ggain : f.centers → I → ℕ → ℝ),
      (∀ p i, EndpointPdoEstimates (c p).index (closedBall x RQ) (Q i).1 (B i)
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold (Q i).1 (W₁ i p))
        (Rnormal p i) Mcap Dendpoint (Dgain p i) (Ggain p i)) →
      (∀ p i (o : Fin 2), ∃ R N,
        GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) (Q i).1 (B i) o)) R N ∧
        ∀ j ξ is, is.length ≤ j → ∀ z,
          (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*threshold) (Q i).1 (B i) o) ξ) z‖ ≤
            Dalgebraic j * (1+cNorm (closedBall x RQ) (j+1) (Q i).1+cNorm (closedBall x RQ) (j+1) (B i))) →
    ∀ (alo ahi : ℝ), 0 < alo → 0 < ahi →
      (∀ p i, cNorm
        (closedBall ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius) ×ˢ closure Vwhole) 2
        (Function.uncurry (fun y b ↦ φ i (physicalCoordinates (c p).index y) b)) ≤ Aphase 2) →
      (∀ p i j q, q ∈
        closedBall ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius) ×ˢ closure Vwhole →
        ‖iteratedFDeriv ℝ j (Function.uncurry (fun y b ↦ φ i (physicalCoordinates (c p).index y) b)) q‖ ≤
          Aphase j * L i^(j-Rstar)) →
      (∀ p i b, b ∈ Vwhole → ∀ y ∈
        ball ((physicalCoordinates (c p).index).symm x) (3*f.physicalRadius),
        alo ≤ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (c p).index z) b) y‖ ∧
          ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (c p).index z) b) y‖ ≤ ahi) →
      (∀ i, cNorm (closedBall x (3*f.physicalRadius) ×ˢ closure Vwhole) 2
        (Function.uncurry (φ i)) ≤ Aphase 2) →
      (∀ i j q, q ∈ closedBall x (3*f.physicalRadius) ×ˢ closure Vwhole →
        ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i^(j-Rstar)) →
      (∀ i b, b ∈ Vwhole → ∀ y ∈ ball x (3*f.physicalRadius),
        alo ≤ ‖fderiv ℝ (fun z ↦ φ i z b) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z b) y‖ ≤ ahi) →
    ∀ (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0),
      (∀ i b, b ∉ Csrc → ∀ y, a i (y,b) = 0) →
    ∀ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) →
      (∀ i b, b ∈ Vwhole → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) b w
        ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s*Adata i*K i^(s+l-Rsource)) →
    ∀ letter : (f.centers × Fin 3) ⊕ Unit,
      ReservedLetterBounds Vwhole
        (fun i b ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y b)
          ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
          (measuredOperator χout χin hχout.continuous hχin hbχout hbχin
            (selectedFullPairedResidualTerm f hK₀ threshold (Q i).1 (B i) (W₁ i)
              output ho.continuous hob hib (retarded i) letter))
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hcχout.isCompact (has i) [] b)))
        Adata K Rsource := by
  classical
  intro c z U O D Z KP KPwhole PInactive Ksigned β
    hmaskBox hcone hsel hcoverage htimePlateau heχp heχpWhole
  have hretarded (p : f.centers) := exists_physical_history_retarded_measured_word_bounds
    (I := I) (BWhole := BWhole p) T (χp p) (hcχp p) f p
    (hprotect p) (hbufferTarget p) (hsrcBuffer p) (g p) (Rad p)
    (hε p) (hεroot p) (hεbuffer p) (hAp p) (hg p) (hRad p)
    (htime p) (htimeε p) (hsrctime p) hphysical (V p) (hV p) (hVc p) (hVcov p)
    hVwhole hVwholec hVwholecov hCsrc hCsrcV (χinc p) (hχinc p) (hcχinc p) (hsχinc p)
    (haWhole p) (gapInactive p) (hgapInactive p) (a₀ p) (B₀ p) (ha₀ p) (hB₀ p)
    (hm p) (hm1 p) (hMfreq p) (InvBound p) (hInv p)
    output ho hoc hos hob threshold hthreshold (angular p) (hang p) (hangPlateau p)
    (Damp p) (hDamp p) (rectOut p) (rectSource p) (hrectSource p) (base p) (cost p)
    (hlocalout p) (hlocalin p) Gref hr hrR hR ext hextcenter hextradius hBband
    hStar hRstar hcompression hreserve horder basis hν hν1
    (hmaskBox p) (hcone p) (hsel p) (hcoverage p) (htimePlateau p) (heχp p) (heχpWhole p)
  choose Sp hSp hret using hretarded
  have hSp0 (p : f.centers) : 0 ≤ Sp p := by linarith [hSp p]
  let Smax : NNReal := Finset.univ.sup (fun p : f.centers ↦ ⟨Sp p, hSp0 p⟩)
  let S₀ : ℝ := max 2 (Smax : ℝ)
  have hS₀ : 2 ≤ S₀ := le_max_left _ _
  have hSpS (p : f.centers) : Sp p ≤ S₀ := by
    have h : (⟨Sp p, hSp0 p⟩ : NNReal) ≤ Smax :=
      Finset.le_sup (f := fun p : f.centers ↦ (⟨Sp p, hSp0 p⟩ : NNReal)) (Finset.mem_univ p)
    exact (show Sp p ≤ (Smax : ℝ) from h).trans (le_max_right _ _)
  refine ⟨S₀,hS₀,?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L sourcePhase h Φ chart G
    hbuffer hsm hdiff hnear hphase hsourceTime Fs matrix Ws
    hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hsourceBandWhole hradial
    Op hOp κ raw hraw hκ hstat hHess hsegments hangle
    lam K Adata hlam hLK hscale hAdata φ hφ heq
    χout χin hχout hcχout hχin hbχout hbχin hplateau hSUchart hSU
    hK₀ hib W₁ retarded hretardedEq hΩ hRQ hball hft hc hdom
    AQ AB Aphase Dendpoint Dalgebraic Wcost hAQ hAB hAphase hDendpoint hDalgebraic hWcost
    hQΩ hBΩ hmap hQl hBl hQp hBp hW₁ hWbudget Rnormal Dgain Ggain hendpoint halgebraic
    alo ahi halo hahi hcapChart hφjetsChart hbandChart hcap hφjets hband
    a ha has hparam Csource hCsource hfourier letter
  have hL (i : I) : 1 ≤ L i :=
    one_le_currentCoefficientScale (by linarith [hS₀.trans (hR₀ i)]) (n i)
  have hRorig : Rsource + fullLowReserve (d+1) + 3 ≤ Rstar := by omega
  have hQp' (i : I) (j : ℕ) :
      cNorm (closedBall x RQ) j (Q i).1 ≤ AQ j * L i^(j-Rstar) := by
    exact (hQp i j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hL i) (by omega)) (hAQ j))
  have hBp' (i : I) (j : ℕ) :
      cNorm (closedBall x RQ) j (B i) ≤ AB j * L i^(j-Rstar) := by
    exact (hBp i j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hL i) (by omega)) (hAB j))
  cases letter with
  | inl pair =>
    rcases pair with ⟨p,k⟩
    fin_cases k
    · exact endpoint_paired_measured_word_bounds f p hK₀ hΩ hball
        threshold hthreshold hft output ho hoc hos hbufferTarget hsrcBuffer ra rb hcoverage
        hν hν1 halo hahi basis hVwhole hVwholec subset_closure Rsource Rstar rStar
        hRorig hreserve AQ AB Aphase Dendpoint Wcost hAQ hAB hAphase hDendpoint hWcost
        lam L K Adata hlam hL hLK hscale hAdata (fun i ↦ (Q i).1) B hQΩ hQp hBp
        W₁ hW₁ hWbudget (Rnormal p) (Dgain p) (Ggain p) (hendpoint p)
        φ hφ (hcapChart p) (hφjetsChart p) (hbandChart p)
        (tsupport χout) hcχout.isCompact hSU a ha has Csource hCsource hfourier
        χout χin hχout hcχout hχin hbχout hbχin hplateau hob hib retarded
    · have hprimary (i : I) : ContDiff ℝ ∞
          (fun q : E × Par ↦ χp p q * sourcePhase p false i q.1 q.2) := by
        have he : (fun q : E × Par ↦ χp p q * sourcePhase p false i q.1 q.2) =
            (fun q : E × Par ↦ φ i (physicalCoordinates (c p).index q.1) q.2) := by
          funext q
          exact (heq p i q.2 q.1).symm
        rw [he]
        exact (hφ i).comp
          (((physicalCoordinates (c p).index).contDiff.comp contDiff_fst).prodMk contDiff_snd)
      exact hret p R₀ n u ell (fun i ↦ (hSpS p).trans (hR₀ i)) hu Q hQ
        (h p) (Φ p) (chart p) (G p) (hbuffer p) (hsm p) (hdiff p) (hnear p)
        (hphase p) (hsourceTime p) (hFs p) (hmatrix p) (hsupport p) (hGsolver p)
        (hGres p) (hbudget p) (hsourceBand p) (hsourceBandWhole p) (hradial p)
        (Op p) (hOp p) (κ p) (hraw p) (hκ p) (hstat p) (hHess p) (hsegments p) (hangle p)
        lam K Adata hlam hLK hscale hAdata (tsupport χout) hcχout.isCompact (hSUchart p)
        a ha has Csource (fun i q hq ↦ hparam i q.2 hq q.1) hCsource hfourier
        hprimary (fun i b y ↦ φ i y b)
        (fun i b ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const)) (heq p)
        χout χin hχout hcχout hχin hbχout hbχin hplateau hK₀ hib W₁ retarded (hretardedEq p)
    · exact algebraic_paired_measured_word_bounds f p hK₀ hΩ hRQ hball hc hdom
        threshold hft output ho hoc hos hν hν1 halo hahi basis hVwhole hVwholec subset_closure
        Rsource Rstar rStar hRorig hreserve AQ AB Aphase Dalgebraic hAQ hAB hAphase hDalgebraic
        lam L K Adata hlam hL hLK hscale hAdata (fun i ↦ (Q i).1) B
        hQΩ hBΩ hmap hQp hBp (halgebraic p) φ hφ (hcapChart p) (hφjetsChart p) (hbandChart p)
        (tsupport χout) hcχout.isCompact hSU a ha has Csource hCsource hfourier
        χout χin hχout hcχout hχin hbχout hbχin hplateau hob hib W₁ retarded
  | inr singleton =>
    cases singleton
    exact elliptic_paired_measured_word_bounds f hK₀ hΩ hball output ho hoc hos hob
      threshold hft basis hVwhole hVwholec subset_closure Rsource Rstar hRorig
      AQ AB Aphase hAQ hAB hAphase hν hν1 halo hahi lam L K Adata hlam hL hLK hscale hAdata
      (fun i ↦ (Q i).1) B hQΩ hBΩ hmap hQl hBl hQp' hBp' φ hφ hcap hφjets hband
      (tsupport χout) hcχout.isCompact hSU a ha has Csource hfourier
      χout χin hχout hcχout hχin hbχout hbχin hplateau hib W₁ retarded

end JanetCartan.PhysicalEllipticWords
