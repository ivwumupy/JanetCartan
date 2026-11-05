module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicComplete
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicInactiveSupplied
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicPartition
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.FourierProfiles

/-!
# Actual complete retarded bounds on the original whole source

Apply the checked active and inactive constructors to the exact original
parameter partition. Both branches retain the same source, history, operator,
phase cutoff and full elapsed interval. No branch response estimate is assumed.
The original signed initializer supplies the stationary and angular geometry;
its realization is a separate obligation of the physical parent construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 6000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
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

/-- The actual retained active and inactive producers yield a reserved bound
for the whole original source. The original scalar parameter cutoff is applied
by the proved Fourier cutoff producer; its closed support allows the active
estimate to be extended without changing its constants. The only local inputs
are the original stationary geometry, original inactive angular gap and actual
operator symbol certificates, not any output norm estimate.
Consumer: `actual_finite_residual_word_reserved_bounds_of_one_step`, including
its SAME final solver step (`app:ch_response:eq:response-whole-source-partition`,
`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_physical_history_whole_source_retarded_reserved_bounds (negative : Bool)
    (T : PatchQuantitativeFamily P Uref hUref)
    (χp : E × Par → ℝ) (hcχp : HasCompactSupport χp)
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost)
    (hbufferTarget : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcBuffer : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {ε aperture g Rad timeRadius : ℝ} (hε : 0 < ε)
    (hεroot : ε ≤ (f.chart p).rootRadius) (hεbuffer : ε ≤ (f.chart p).bufferRadius/8)
    (hAp : 0 < aperture) (hg : 0 < g) (hRad : 0 < Rad)
    (htime : 0 < timeRadius) (htimeε : timeRadius ≤ ε)
    (hsrctime : (f.chart p).maskRadius ≤ timeRadius)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    {V : Set Par} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVcov : ∀ q ∈ closure V,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {Vwhole Csrc : Set Par} (hVwhole : IsOpen Vwhole)
    (hVwholec : IsCompact (closure Vwhole))
    (hVwholecov : ∀ q ∈ closure Vwhole,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    (hCsrc : IsClosed Csrc) (hCsrcV : Csrc ⊆ Vwhole)
    (χinc : Par → ℝ) (hχinc : ContDiff ℝ ∞ χinc)
    (hcχinc : HasCompactSupport χinc) (hsχinc : tsupport χinc ⊆ V)
    {aWhole BWhole gapInactive : ℝ} (haWhole : 0 < aWhole)
    (hgapInactive : 0 < gapInactive)
    {a₀ B₀ m Mfreq : ℝ} (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (hm : 0 < m) (hm1 : m ≤ 1) (hMfreq : 1 ≤ Mfreq)
    (InvBound : ℝ) (hInv : 0 ≤ InvBound)
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
    let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture g Rad
    let D := retainedOpenIntegrationDomain z ε O
    let Z := Ioo (-2*timeRadius) (2*timeRadius) ×ˢ (U ×ˢ V)
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ closure V
    let KPwhole := closure (elapsedPhysicalBox z ε) ×ˢ closure Vwhole
    let PInactive := Csrc ∩ tsupport (fun b ↦ 1-χinc b)
    let Ksigned := fullSourceSignedCarrier z ε (closure V) O
    let β := selectedEndpointMultiplier f p threshold
    let _π : E → ℂ := fun ξ ↦ annularSelector (a₀/(2*Mfreq)) (2*B₀/m) (by positivity) (by positivity) ξ
    MapsTo (primaryCoordinateChange c.index) (tsupport f.inputMask ∪ tsupport f.outputMask) U →
    (tsupport (f.angularMask p ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone c.radialSection z.2.2 (ε/4) (aperture/2)) →
    (retainedAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture
      (retainedSelectorGap z.2.2 (ε/2) aperture (a₀/(2*Mfreq))) (2*(2*B₀/m)) ⊆ O) →
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb β →
    (∀ y, endpointOutputMask f p output y ≠ 0 → c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) →
    (∀ q ∈ KP, χp =ᶠ[𝓝 q] (fun _ ↦ 1)) →
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
    let sourcePhase := fun i ↦ if negative then T.negativeFullSourcePhaseInCoordinates c.index (Q i)
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
    (∀ i q, q ∈ KP → a₀ ≤ ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ∧
      ‖fderiv ℝ (fun y ↦ T.fullSourcePhaseInCoordinates c.index (Q i) y q.2) q.1‖ ≤ B₀) →
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
    let capped := fun i o ↦ Mo.comp ((Op i o).comp Mi)
    ∀ κ : I → (ℝ × (E × Par)) → CW,
    let raw := fun i ↦ fullSourceJointPhase false (curriedPhase c.radialSection (chart i))
      (sourcePhase i)
    (∀ i, ContDiffOn ℝ ∞ (raw i) (Z ×ˢ D)) →
    (∀ i, ContDiffOn ℝ ∞ (κ i) Z) →
    (∀ i q, q ∈ Z → κ i q ∈ D ∧
      gradient (fun w ↦ raw i (q,w)) (κ i q) = 0 ∧ raw i (q,κ i q) = 0) →
    (∀ i q, q ∈ Z → ∀ w ∈ closure D,
      let phase := fun b w ↦ raw i ((q.1,b),w)
      IsUnit (averagedPhaseHessian phase (fun b ↦ κ i (q.1,b)) q.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian phase (fun b ↦ κ i (q.1,b)) q.2 w)‖ ≤ InvBound) →
    (∀ i q, q ∈ Z → ∀ w ∈ closure D,
      ∀ t ∈ uIcc (0 : ℝ) q.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((t,q.2),κ i q + a • (w-κ i q)) ∈ Ksigned) →
    (∀ i b, b ∈ Vwhole → b ∈ PInactive → ∀ t ∈ Icc 0 (3*c.maskRadius/4),
      ∀ y ∈ U, ∀ ξ ∈ tsupport β,
      gapInactive ≤ dist (NormedSpace.normalize (gradient (fun y ↦ sourcePhase i y b) y))
        (NormedSpace.normalize ξ)) →
    ∀ (lam K A₀ : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ A₀ i) →
    ∀ (S : Set E) (hS : IsCompact S), S ⊆ U →
    ∀ (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ),
    (∀ i q, q.2 ∉ Csrc → a i q = 0) →
    (∀ l s, 0 ≤ Csource l s) →
    (∀ i c, c ∈ Vwhole → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A₀ i*K i^(s+l-Rsource)) →
    let φ := fun i c y ↦ χp (y,c)*sourcePhase i y c
    ∀ hprimary : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1),
    ∀ o : Fin 2, ReservedLetterBounds Vwhole
      (fun i b ↦ demodulatedL2Operator (lam i) (φ i b)
        ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
        (capped i o) (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b)))
      (fun i ↦ lam i ^ (-(o.val : ℤ))*A₀ i) K Rsource := by
  intro c z U O D Z KP KPwhole PInactive Ksigned β π
    hmaskBox hcone hsel hcoverage htimePlateau heχp heχpWhole
  obtain ⟨SA,hSA,hactive⟩ :=
    exists_physical_history_complete_retarded_reserved_envelopes (I := I) negative T χp hcχp
      f p hprotect hbufferTarget hsrcBuffer hε hεroot hεbuffer hAp hg hRad htime htimeε
      hsrctime hphysical hV hVc hVcov ha₀ hB₀ hm hm1 hMfreq InvBound hInv
      output ho hoc hos hob threshold hthreshold angular hang hangPlateau Damp hDamp
      χout χsource hχsource base cost hlocalout hlocalin Gref hr hrR hR ext hextcenter
      hextradius hBband hStar hRstar hcompression hreserve horder basis hν hν1
      hmaskBox hcone hsel hcoverage htimePlateau heχp
  obtain ⟨SI,hSI,hinactive⟩ :=
    exists_physical_history_inactive_capped_envelopes_for_supplied_cutoff (I := I)
      (g := g) (Rad := Rad) (B₀ := BWhole) (Mfreq := Mfreq) false T χp
      f p hprotect hbufferTarget hsrcBuffer hε hεroot hεbuffer hAp hg htimeε
      hsrctime hphysical hVwhole hVwholec hVwholecov haWhole hm hm1 (by linarith)
      output ho hoc hos hob threshold hthreshold angular hang hangPlateau Damp hDamp
      χout χsource hχsource base cost hlocalout hlocalin Gref hr hrR hR ext hextcenter
      hextradius hBband hStar (by omega) hRstar hreserve horder hν hν1
      hmaskBox hcone hcoverage htimePlateau heχpWhole
  refine ⟨max SA SI,hSA.trans (le_max_left _ _),?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L sourcePhase h Φ chart G
    hbuffer hsm hdiff hnear hphase hsourceTime Fs matrix Ws
    hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hsourceBandWhole hradial
    Op hOp e Mo Mi capped κ raw hraw hκ hstat hHess hsegments hangle
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hparam hCsource hfourier
    φ hprimary o
  have hSAi i : SA ≤ R₀ i := (le_max_left _ _).trans (hR₀ i)
  have hSIi i : SI ≤ R₀ i := (le_max_right _ _).trans (hR₀ i)
  have hL i : 1 ≤ L i := one_le_currentCoefficientScale (by linarith [hSAi i]) (n i)
  have hK i : 1 ≤ K i := (hL i).trans (hLK i)
  have hglobal := reserved_source_fourier_profile_global_of_closed_parameter_support
    hCsrc hCsrcV a hparam A₀ K hA₀ (fun i ↦ (zero_le_one.trans (hK i)))
    Rsource Csource hCsource hfourier
  obtain ⟨Ccut,hCcut,hcut⟩ := exists_reserved_source_fourier_profiles_cutoff_and_complement
    χinc hχinc hcχinc Csource
  have hcutAll := hcut a ha A₀ K hA₀ hK Rsource Set.univ
    (fun i b _ ↦ hglobal i b)
  let aActive : I → E × Par → Fibre := fun i q ↦ χinc q.2 • a i q
  let aInactive : I → E × Par → Fibre := fun i q ↦ (1-χinc q.2) • a i q
  have haActive i : ContDiff ℝ ∞ (aActive i) := (hχinc.comp contDiff_snd).smul (ha i)
  have haInactive i : ContDiff ℝ ∞ (aInactive i) :=
    (contDiff_const.sub (hχinc.comp contDiff_snd)).smul (ha i)
  have hsActive i q (hq : q.1 ∉ S) : aActive i q = 0 := by
    change χinc q.2 • a i q = 0
    rw [has i q hq,smul_zero]
  have hsInactive i q (hq : q.1 ∉ S) : aInactive i q = 0 := by
    change (1-χinc q.2) • a i q = 0
    rw [has i q hq,smul_zero]
  have hfourierActive i b (_hb : b ∈ V) l (w : Fin l → Par)
      (hw : ∀ j, ‖w j‖ ≤ 1) (s : ℕ) := hcutAll false i b (Set.mem_univ _) l w hw s
  have hfourierInactive i b (_hb : b ∈ Vwhole) l (w : Fin l → Par)
      (hw : ∀ j, ‖w j‖ ≤ 1) (s : ℕ) :
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ aInactive i (y,q)) b w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Ccut l s*A₀ i*K i^(s+l) := by
    obtain ⟨hf,hm,hb⟩ := hcutAll true i b (Set.mem_univ _) l w hw s
    refine ⟨hf,hm,hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hK i) (Nat.sub_le _ _))
      (mul_nonneg (hCcut l s) (hA₀ i))
  have hparamActive i b (hb : b ∉ tsupport χinc) (y : E) : aActive i (y,b) = 0 := by
    change χinc b • a i (y,b) = 0
    rw [image_eq_zero_of_notMem_tsupport hb,zero_smul]
  have hparamInactive i b (hb : b ∉ PInactive) (y : E) : aInactive i (y,b) = 0 := by
    by_cases hc : b ∈ Csrc
    · have hn : b ∉ tsupport (fun b ↦ 1-χinc b) := fun hh ↦ hb ⟨hc,hh⟩
      have hz : 1-χinc b = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun b : Par ↦ 1-χinc b) hn
      change (1-χinc b) • a i (y,b) = 0
      rw [hz,zero_smul]
    · change (1-χinc b) • a i (y,b) = 0
      rw [hparam i (y,b) hc,smul_zero]
  have hpartition i q : a i q = aActive i q+aInactive i q := by
    change a i q = χinc q.2 • a i q+(1-χinc q.2) • a i q
    rw [← add_smul]
    have hc : χinc q.2+(1-χinc q.2) = 1 := by ring
    rw [hc,one_smul]
  have hφ i : ContDiff ℝ ∞ (Function.uncurry (φ i)) :=
    (hprimary i).comp (contDiff_snd.prodMk contDiff_fst)
  let X := Prod.fst '' tsupport χp
  have hX : IsCompact X := hcχp.image continuous_fst
  have hφs i b : tsupport (φ i b) ⊆ X := by
    apply closure_minimal _ hX.isClosed
    intro y hy
    have hy' : χp (y,b)*sourcePhase i y b ≠ 0 := hy
    exact ⟨(y,b),subset_tsupport χp ((mul_ne_zero_iff.mp hy').1),rfl⟩
  let active := fun i b ↦ demodulatedL2Operator (lam i) (φ i b)
    ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
    (capped i o) (graphTestToLp (vectorOriginalDatumTest (aActive i) (haActive i) hS (hsActive i) [] b))
  have hactiveSmooth i : ContDiffOn ℝ ∞ (active i) V :=
    contDiffOn_demodulated_supported_operator hV hS hX (aActive i) (haActive i)
      (hsActive i) (lam i) (φ i) (hφ i) (fun b _ ↦ hφs i b) (capped i o)
  have hactiveBounds : ReservedLetterBounds V active
      (fun i ↦ lam i^(-(o.val : ℤ))*A₀ i) K Rsource := by
    refine ⟨hactiveSmooth,?_⟩
    intro ps hps s
    obtain ⟨C,hC,hb⟩ := hactive R₀ n u ell hSAi hu Q hQ h Φ chart G hbuffer hsm hdiff
      hnear hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget
      hsourceBand hradial Op hOp κ hraw hκ hstat hHess hsegments
      lam K A₀ hlam hLK hscale hA₀ S hS hSU aActive haActive hsActive
      Ccut hCcut hfourierActive hprimary o s ps hps
    refine ⟨C,hC,?_⟩
    intro i b hbV
    simpa only [active,mul_assoc] using hb i b hbV
  have hradialMask i t (ht : t ∈ Icc (0 : ℝ) c.maskRadius) y (hy : y ∈ U)
      ξ (hξ : ξ ∈ retainedFrequencyDomain c.radialSection z ε aperture (1/2)) :=
    hradial i t ⟨ht.1,ht.2.trans (hsrctime.trans htimeε)⟩ y hy ξ hξ
  have hprimaryI : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ if negative then
      -(χp q*T.fullSourcePhaseInCoordinates c.index (Q i) q.1 q.2)
      else χp q*T.fullSourcePhaseInCoordinates c.index (Q i) q.1 q.2) := by
    intro i
    simpa only [φ,sourcePhase,PatchQuantitativeFamily.negativeFullSourcePhaseInCoordinates,
      ite_apply,mul_ite,mul_neg] using hprimary i
  have hInactiveResult := hinactive R₀ n u ell hSIi hu Q hQ h Φ chart G hbuffer hsm hdiff
    hnear hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget hsourceBandWhole
    hradialMask Op hOp negative PInactive (hCsrc.inter (isClosed_tsupport _)) gapInactive
    hgapInactive (by
      simpa only [sourcePhase,ite_apply,PatchQuantitativeFamily.negativeFullSourcePhaseInCoordinates,
        Bool.false_eq_true,ite_false] using hangle)
    lam K A₀ hlam hLK hscale hA₀ S hS hSU aInactive haInactive
    hsInactive Ccut hfourierInactive hparamInactive hprimaryI o
  let inactive := fun i b ↦ demodulatedL2Operator (lam i) (φ i b)
    ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
    (capped i o) (graphTestToLp (vectorOriginalDatumTest (aInactive i) (haInactive i) hS (hsInactive i) [] b))
  have hI : (∀ i, ContDiffOn ℝ ∞ (inactive i) Vwhole) ∧
      ∀ (s : ℝ) (k : ℕ) (q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i b, b ∈ Vwhole →
        ∀ w : Fin k → Par, (∀ j, ‖w j‖ ≤ 1) →
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k (inactive i) b w) ∧
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (inactive i) b w) ≤
          C*A₀ i*lam i^(-q) := by
    simpa only [inactive,φ,sourcePhase,PatchQuantitativeFamily.negativeFullSourcePhaseInCoordinates,
      ite_apply,mul_ite,mul_neg,Bool.false_eq_true,ite_false] using hInactiveResult
  have hinactiveBounds := reserved_letter_bounds_of_arbitrary_precision hVwhole inactive
    hI.1 lam A₀ K (-(o.val : ℤ)) Rsource hlam hA₀ hK hI.2
  exact whole_source_reserved_bounds_of_parameter_partition hV hVwhole (isClosed_tsupport χinc) hsχinc
    a aActive aInactive ha haActive haInactive hS has hsActive hsInactive hpartition hparamActive
    lam (fun i ↦ lam i^(-(o.val : ℤ))*A₀ i) K Rsource
    (fun i ↦ mul_nonneg (zpow_nonneg (by linarith [hlam i]) _) (hA₀ i))
    (fun i ↦ zero_le_one.trans (hK i)) φ
    (fun i b ↦ (hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
    (fun i ↦ capped i o) hactiveBounds hinactiveBounds

end JanetCartan.PhysicalPrimary
