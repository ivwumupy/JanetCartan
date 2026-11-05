module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicMeasured
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.CharacteristicCosts

/-!
# The exact retarded letter of the complete original measured alphabet

The normalized physical measured response is the literal `Sum.inl(p,1)`
letter, not an auxiliary retarded replacement. Its inverse-frequency gain may
be discarded only after using `lam ≥ 1`; the natural reserve is unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 6000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalPrimary
open FixedDomainInverse FixedDomainInverse.ReservedRetardedNear
open ResponseTransfer RetainedCharacteristicEnvelopes
open FullSourceEnvelopes RegularSector.Characteristic.ResidualCoordinates
open ActualCarriers ActualCarriers.CurrentFullPhase HamiltonPhase FrozenMenu CompatibleResponse
open RegularSector.Characteristic ConicPhase EvolutionIntegral AmplitudeBounds SymbolBudgets
open Pseudodifferential FourierIntegral FullLowBounds LowBounds SourceExpansion
open NormalComparison FrequencyCutoff AmplitudeBound FullAmplitudePrimitiveBudget.Local
open DirectEvolution CompactTransfer BranchAmplitudes ModifiedLow AnnularComplement AnnularSobolev
open JanetCartan.ResponseTransfer.Complement UniformEvolution IntegratedEnvelope RegularSector.FiniteMasks
open RetainedFactors WholeImageGeometry FullSourceStationary
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.AlgebraicChart
open RegularSector.FiniteAssembly RegularSector.FiniteAlgebraic RegularSector.FinitePdo
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles ConicAmplitude
variable {d : ℕ} {I ι : Type} [Fintype ι]
variable {P : Patch (d+1)} {Uref : Set (Euclidean (d+1))} {hUref : IsOpen Uref}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d+1)
local notation "Fibre" => EuclideanSpace ℂ (Fin (d+1))
local notation "TC" => RegularSector.Characteristic.TwoTimePoint (Euclidean d)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ Mcap : ℝ} {K₀ : Set (Euclidean (d+1))}

open PhysicalEllipticWords CharacteristicPartition ParameterSourceCutoffs FiniteResidualWordProfiles

open FixedDomainInverse.FiniteResidualEnvelopes RegularSector.NormalizedSolver

open ArbitraryAccuracy.SelectedLocalization RegularSector.FiniteEvolution

open RegularSector.FiniteResidual.FiniteIdentity RegularSector.FiniteAssembly

/-- Construct the missing actual retarded case of the complete measured
alphabet directly from its signed native stationary geometry and the original
retarded certificate. No response bound or intermediate-word estimate is an
input. Consumer: `hstep` in
`actual_finite_residual_word_reserved_bounds_of_one_step`, joining the endpoint,
algebraic and elliptic cases on the SAME full inverse
(`energy-complete-residual`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_physical_history_retarded_measured_word_bounds
    (T : PatchQuantitativeFamily P Uref hUref)
    (χp : E × Par → ℝ) (hcχp : HasCompactSupport χp)
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost)
    (hbufferTarget : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcBuffer : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {ε aperture timeRadius : ℝ} (g Rad : Bool → ℝ) (hε : 0 < ε)
    (hεroot : ε ≤ (f.chart p).rootRadius) (hεbuffer : ε ≤ (f.chart p).bufferRadius/8)
    (hAp : 0 < aperture) (hg : ∀ negative, 0 < g negative) (hRad : ∀ negative, 0 < Rad negative)
    (htime : 0 < timeRadius) (htimeε : timeRadius ≤ ε)
    (hsrctime : (f.chart p).maskRadius ≤ timeRadius)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    (V : Bool → Set Par) (hV : ∀ negative, IsOpen (V negative))
    (hVc : ∀ negative, IsCompact (closure (V negative)))
    (hVcov : ∀ negative, ∀ q ∈ closure (V negative),
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Vwhole Csrc : Set Par} (hVwhole : IsOpen Vwhole)
    (hVwholec : IsCompact (closure Vwhole))
    (hVwholecov : ∀ q ∈ closure Vwhole,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hCsrc : IsClosed Csrc) (hCsrcV : Csrc ⊆ Vwhole)
    (χinc : Bool → Par → ℝ) (hχinc : ∀ negative, ContDiff ℝ ∞ (χinc negative))
    (hcχinc : ∀ negative, HasCompactSupport (χinc negative))
    (hsχinc : ∀ negative, tsupport (χinc negative) ⊆ V negative)
    {aWhole BWhole : ℝ} (haWhole : 0 < aWhole)
    (gapInactive : Bool → ℝ) (hgapInactive : ∀ negative, 0 < gapInactive negative)
    (a₀ B₀ : Bool → ℝ) {m Mfreq : ℝ}
    (ha₀ : ∀ negative, 0 < a₀ negative) (hB₀ : ∀ negative, 0 < B₀ negative)
    (hm : 0 < m) (hm1 : m ≤ 1) (hMfreq : 1 ≤ Mfreq)
    (InvBound : Bool → ℝ) (hInv : ∀ negative, 0 ≤ InvBound negative)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : Euclidean d → ℝ) (hang : ContDiff ℝ ∞ angular)
    (hangPlateau : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (Damp : ℕ → ℝ) (hDamp : ∀ j, 0 ≤ Damp j)
    {ra rb : ℝ}
    (χout χsource : E → ℂ) (hχsource : ContDiff ℝ ∞ χsource)
    (base : Fin 2 → ℝ) (cost : Fin 2 → ℕ → ℝ)
    (hlocalout : ∀ y, (output y : ℂ)*χout ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ))
    (hlocalin : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y)*(f.inputMask y : ℂ) =
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
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2,(coordinateSplit c.index p.val.val).2))
    let U := elapsedPhysicalBox z (ε/2)
    let O := fun negative ↦ retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2
      (ε/2) aperture (g negative) (Rad negative)
    let D := fun negative ↦ retainedOpenIntegrationDomain z ε (O negative)
    let Z := fun negative ↦ Ioo (-2*timeRadius) (2*timeRadius) ×ˢ (U ×ˢ V negative)
    let KP := fun negative ↦ closure (elapsedPhysicalBox z ε) ×ˢ closure (V negative)
    let KPwhole := closure (elapsedPhysicalBox z ε) ×ˢ closure Vwhole
    let PInactive := fun negative ↦ Csrc ∩ tsupport (fun b ↦ 1-χinc negative b)
    let Ksigned := fun negative ↦ fullSourceSignedCarrier z ε (closure (V negative)) (O negative)
    let β := selectedEndpointMultiplier f p threshold
    MapsTo (primaryCoordinateChange c.index) (tsupport f.inputMask ∪ tsupport f.outputMask) U →
    (tsupport (f.angularMask p ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone c.radialSection z.2.2 (ε/4) (aperture/2)) →
    (∀ negative, retainedAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture
      (retainedSelectorGap z.2.2 (ε/2) aperture (a₀ negative/(2*Mfreq)))
      (2*(2*B₀ negative/m)) ⊆ O negative) →
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb β →
    (∀ y, endpointOutputMask f p output y ≠ 0 → c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) →
    (∀ negative, ∀ q ∈ KP negative, χp =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    (∀ q ∈ KPwhole, χp =ᶠ[𝓝 q] (fun _ ↦ 1)) →
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧
    ∀ (R₀ : I → ℝ) (n : I → ℕ)
      (u : ∀ i, Fin (n i) → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
      (ell : ∀ i, Fin (n i) → ℕ), (∀ i, S₀ ≤ R₀ i) →
      (∀ i, RevisedGlobal.IsAdmissibleHistory Bband (R₀ i) kMin (u i) (ell i)) →
    ∀ Q : I → {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold},
      (∀ i, (Q i).1 = extendedProjectedStress ext (RevisedGlobal.finiteMap Gref.map (u i))) →
    let B := fun i ↦ reducedZerothProjection (d+1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (RevisedGlobal.finiteMap Gref.map (u i))
    let L := fun i ↦ currentCoefficientScale (R₀ i) (n i)
    let sourcePhase := fun negative i ↦ if negative then T.negativeFullSourcePhaseInCoordinates c.index (Q i)
      else T.fullSourcePhaseInCoordinates c.index (Q i)
    ∀ (h : I → RootState (Euclidean d) → ℝ)
      (Φ : I → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (chart : I → OpenPartialHomeomorph TC TC) (G : I → TC → ℝ),
      (∀ i, closedBall (z.1,z) c.targetRadius ⊆ (chart i).target) →
      (∀ i, ContDiffOn ℝ ∞ (twoTimePhase (chart i)) (chart i).target) →
      (∀ i q, q ∈ (chart i).target →
        HasFDerivAt (twoTimePhase (chart i)) (twoTimePhaseDifferential (h i) (Φ i) (chart i) q) q) →
      (∀ i q, q ∈ closedBall (z.1,z) c.targetRadius → ‖twoTimePhaseMixed (chart i) q - 1‖ ≤ 1/2) →
      (∀ i j, cNorm (closedBall (z.1,z) c.targetRadius) j (twoTimePhase (chart i)) ≤
        c.phaseCost j * (1+cNorm (closedBall x RQ) (j+1) (Q i).1)) →
      (∀ i q, q ∈ (chart i).target → ((chart i).symm q).2.1 = q.2.1) →
    let Fs := fun i ↦ selectedBufferedAmplitude f p (Q i).1 (B i) (Φ i) (chart i)
    let matrix := fun i k ↦ collared c.radialSection (if k=0 then 0 else 1) angular (Fs i k)
    let Ws := fun i ↦ selectedConicAmplitude f p (Q i).1 (B i) (Φ i) (chart i) angular
    (∀ i k, ContDiff ℝ ∞ (Fs i k)) → (∀ i k, ContDiff ℝ ∞ (matrix i k)) →
    (∀ i k, tsupport (matrix i k) ⊆ ConicPhase.domain c.radialSection
      ((chart i).target ∩ (chart i).symm ⁻¹'
        (ball z.1 (c.maskRadius/2) ×ˢ (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2))))) →
    (∀ i q, q ∈ tsupport (matrix i 0) ∪ tsupport (matrix i 1) →
      G i =ᶠ[𝓝 q] phase c.radialSection (chart i)) →
    (∀ i q, c.timeMask =ᶠ[𝓝 q.1] (fun _ ↦ 1) → matrix i 2 q ≠ 0 →
      G i =ᶠ[𝓝 q] phase c.radialSection (chart i)) →
    (∀ i k j, BoundedTwoTimeOrderSeminorm (if k=0 then 0 else 1)
      (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (Ws i k) ∧
      twoTimeOrderSeminorm (if k=0 then 0 else 1)
        (bufferedJetSet c.radialSection z (c.bufferRadius/2) ra rb) j (Ws i k) ≤
        Damp j * (1+cNorm (closedBall x RQ) (j+10) (Q i).1+cNorm (closedBall x RQ) (j+9) (B i))) →
    (∀ negative i q, q ∈ KP negative → a₀ negative ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ≤ B₀ negative) →
    (∀ i q, q ∈ KPwhole →
      aWhole ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ≤ BWhole) →
    (∀ i t, t ∈ Icc 0 ε → ∀ y ∈ U,
      ∀ ξ ∈ retainedFrequencyDomain c.radialSection z ε aperture (1/2),
        m*‖ξ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase c.radialSection (chart i)) t v ξ) y‖ ∧
        ‖fderiv ℝ (fun v ↦ elapsedPhase
          (curriedPhase c.radialSection (chart i)) t v ξ) y‖ ≤ Mfreq*‖ξ‖) →
    ∀ Op : I → Fin 2 → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1),
      (∀ i o, RetainedSignedRetardedBounds (closedBall x RQ) (Q i).1 (B i) (3*c.maskRadius/4)
        (z.1-c.maskRadius/2) (fun t s y ξ ↦ G i (t,(s,(y,ξ))))
        (if o=0 then Ws i 0+Ws i 1 else Ws i 2) χout χsource β hχsource
        o.val (base o) (cost o) (Op i o)) →
    let e := physicalCoordinates c.index
    let Mo := sourceCutMultiplier (r := d+1) (output ∘ e)
      (ho.continuous.comp e.continuous) (fun y ↦ hob (e y))
    let Mi := sourceCutMultiplier (r := d+1) (f.inputMask ∘ e)
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
        simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (f.inputMask_range (e y)).1]
          using (f.inputMask_range (e y)).2)
    let _capped := fun i o ↦ Mo.comp ((Op i o).comp Mi)
    ∀ κ : Bool → I → (ℝ × (E × Par)) → CW,
    let raw := fun negative i ↦ fullSourceJointPhase false (curriedPhase c.radialSection (chart i))
      (sourcePhase negative i)
    (∀ negative i, ContDiffOn ℝ ∞ (raw negative i) (Z negative ×ˢ D negative)) →
    (∀ negative i, ContDiffOn ℝ ∞ (κ negative i) (Z negative)) →
    (∀ negative i q, q ∈ Z negative → κ negative i q ∈ D negative ∧
      gradient (fun w ↦ raw negative i (q,w)) (κ negative i q) = 0 ∧ raw negative i (q,κ negative i q) = 0) →
    (∀ negative i q, q ∈ Z negative → ∀ w ∈ closure (D negative),
      let phase := fun b w ↦ raw negative i ((q.1,b),w)
      IsUnit (averagedPhaseHessian phase (fun b ↦ κ negative i (q.1,b)) q.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian phase (fun b ↦ κ negative i (q.1,b)) q.2 w)‖ ≤ InvBound negative) →
    (∀ negative i q, q ∈ Z negative → ∀ w ∈ closure (D negative),
      ∀ t ∈ uIcc (0 : ℝ) q.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((t,q.2),κ negative i q + a • (w-κ negative i q)) ∈ Ksigned negative) →
    (∀ negative i b, b ∈ Vwhole → b ∈ PInactive negative → ∀ t ∈ Icc 0 (3*c.maskRadius/4),
      ∀ y ∈ U, ∀ ξ ∈ tsupport β,
      gapInactive negative ≤ dist (NormedSpace.normalize (gradient (fun y ↦ sourcePhase negative i y b) y))
        (NormedSpace.normalize ξ)) →
    ∀ (lam K A₀ : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ A₀ i) →
    ∀ (S : Set E) (hS : IsCompact S), physicalCoordinates c.index ⁻¹' S ⊆ U →
    ∀ (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ),
    (∀ i q, q.2 ∉ Csrc → a i q = 0) →
    (∀ l s, 0 ≤ Csource l s) →
    (∀ i c, c ∈ Vwhole → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A₀ i*K i^(s+l-Rsource)) →
    let φ := fun i c y ↦ χp (y,c)*sourcePhase false i y c
    ∀ _hprimary : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1),
    ∀ (φphysical : I → Par → E → ℝ) (hφphysical : ∀ i b, Continuous (φphysical i b)),
      (∀ i b y, φphysical i b (physicalCoordinates c.index y) = φ i b y) →
    ∀ (μ ψ : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (_hμc : HasCompactSupport μ)
      (hψ : Continuous ψ) (hμb : ∀ y, ‖μ y‖ ≤ 1) (hψb : ∀ y, ‖ψ y‖ ≤ 1),
      (∀ y ∈ S, ψ y = 1) →
    ∀ (hK₀ : IsCompact K₀) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
      (W₁all : I → f.centers → TwoTimeAmplitude d (d+1))
      (retarded : I → f.centers → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1)),
      (∀ i, retarded i p = Op i 1) →
    ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (φphysical i b) (hφphysical i b)
        (measuredOperator μ ψ hμ.continuous hψ hμb hψb
          (selectedFullPairedResidualTerm f hK₀ threshold (Q i).1 (B i) (W₁all i)
            output ho.continuous hob hib (retarded i) (Sum.inl (p,1))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b)))
      A₀ K Rsource := by
  intro c z U O D Z KP KPwhole PInactive Ksigned β
    hmaskBox hcone hsel hcoverage htimePlateau heχp heχpWhole
  obtain ⟨S₀,hS₀,hmeasured⟩ := exists_physical_history_measured_paired_retarded_reserved_bounds
    (I := I) (BWhole := BWhole) T χp hcχp f p hprotect hbufferTarget hsrcBuffer
    g Rad hε hεroot hεbuffer hAp hg hRad htime htimeε hsrctime hphysical
    V hV hVc hVcov hVwhole hVwholec hVwholecov hCsrc hCsrcV χinc hχinc hcχinc hsχinc
    haWhole gapInactive hgapInactive a₀ B₀ ha₀ hB₀ hm hm1 hMfreq InvBound hInv
    output ho hoc hos hob threshold hthreshold angular hang hangPlateau Damp hDamp
    χout χsource hχsource base cost hlocalout hlocalin Gref hr hrR hR ext hextcenter
    hextradius hBband hStar hRstar hcompression hreserve horder basis hν hν1
    hmaskBox hcone hsel hcoverage htimePlateau heχp heχpWhole
  refine ⟨S₀,hS₀,?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L sourcePhase h Φ chart G
    hbuffer hsm hdiff hnear hphase hsourceTime Fs matrix Ws
    hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hsourceBandWhole hradial
    Op hOp e Mo Mi capped κ raw hraw hκ hstat hHess hsegments hangle
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hparam hCsource hfourier
    φ hprimary φphysical hφphysical heq μ ψ hμ hμc hψ hμb hψb hinput
    hK₀ hib W₁all retarded hretarded
  have hp := hmeasured R₀ n u ell hR₀ hu Q hQ h Φ chart G hbuffer hsm hdiff hnear
    hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand
    hsourceBandWhole hradial Op hOp κ hraw hκ hstat hHess hsegments hangle
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hparam hCsource hfourier
    hprimary φphysical hφphysical heq μ ψ hμ hμc hψ hμb hψb hinput (1 : Fin 2) (1 : ℂ)
  change ReservedLetterBounds Vwhole
    (fun i b ↦ demodulatedL2Operator (lam i) (φphysical i b) (hφphysical i b)
      (measuredOperator μ ψ hμ.continuous hψ hμb hψb
        (RegularSector.FiniteEvolution.physicalOperator c.index
          (normalizedPair ((1 : ℂ) • capped i (1 : Fin 2)))))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b)))
    (fun i ↦ lam i ^ (-1 : ℤ)*A₀ i) K Rsource at hp
  have he i : RegularSector.FiniteEvolution.physicalOperator c.index
      (normalizedPair ((1 : ℂ) • capped i (1 : Fin 2))) =
      selectedFullPairedResidualTerm f hK₀ threshold (Q i).1 (B i) (W₁all i)
        output ho.continuous hob hib (retarded i) (Sum.inl (p,1)) := by
    rw [selectedFullPairedResidualTerm_characteristic]
    change RegularSector.FiniteEvolution.physicalOperator c.index
        (normalizedPair ((1 : ℂ) • capped i (1 : Fin 2))) =
      normalizedPair (RegularSector.FiniteEvolution.physicalOperator c.index
        (selectedCommonChartRetarded f p output ho.continuous hob hib (retarded i p)))
    rw [hretarded i]
    have hcap : selectedCommonChartRetarded f p output ho.continuous hob hib (Op i 1) =
        capped i (1 : Fin 2) := by
      rfl
    rw [hcap]
    simpa only [one_smul] using
      physicalOperator_normalized_scalar_pair c.index (capped i (1 : Fin 2)) (1 : ℂ)
  have hK i : 0 ≤ K i := zero_le_one.trans
    ((one_le_currentCoefficientScale (by linarith [hS₀.trans (hR₀ i)]) (n i)).trans (hLK i))
  have hp' : ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (φphysical i b) (hφphysical i b)
        (measuredOperator μ ψ hμ.continuous hψ hμb hψb
          (selectedFullPairedResidualTerm f hK₀ threshold (Q i).1 (B i) (W₁all i)
            output ho.continuous hob hib (retarded i) (Sum.inl (p,1))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b)))
      (fun i ↦ lam i ^ (-1 : ℤ)*A₀ i) K Rsource := by
    simpa only [he] using hp
  exact hp'.discard_inverse_frequency hlam hA₀ hK

end JanetCartan.PhysicalPrimary
