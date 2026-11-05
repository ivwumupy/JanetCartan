module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicNear
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicComplement
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.Basic
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PdoReassembly
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAnnular
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicWholeImage

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedRetardedNear.PhysicalIncidence
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedRetardedNear.SignedPhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedHistoryEnvelopes

/-!
# Complete physical retarded operators with the original reserve

Use a supplied cutoff of the original signed source, construct the annular
amplitude profiles, raw signed phase profiles and whole-image geometry from
the selected history producers, and apply the actual finite-jet retarded theorem. The source reserve is fixed before derivative
orders and accuracy; every original physical mask and the full elapsed interval
is retained. The original initializer supplies the signed stationary maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
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

/-- Reassemble the SAME complete selected physical retarded operator for
either original source sign. The actual reserved near constructor and the
actual complementary-frequency producer are applied, not assumed. Every
original elapsed interval, cutoff and coefficient family is unchanged. The cutoff plateau and smooth capped source are
provided by `exists_physical_history_signed_incidence_profiles`.
Primitive phase, amplitude, normal geometry and annular supports are constructed;
finite compression is used only through total order `s+|ps|`. No near-envelope
estimate or all-order replacement scale is a premise.
Consumer: reserved full residual-word induction in
`app:ch_response:eq:response-graded-reduced`. -/
theorem exists_physical_history_complete_retarded_reserved_envelopes (negative : Bool)
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
    ∀ (lam K A₀ : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ A₀ i) →
    ∀ (S : Set E) (hS : IsCompact S), S ⊆ U →
    ∀ (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ),
    (∀ l s, 0 ≤ Csource l s) →
    (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A₀ i*K i^(s+l-Rsource)) →
    let φ := fun i c y ↦ χp (y,c)*sourcePhase i y c
    ∀ hprimary : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1),
    ∀ o : Fin 2, ∀ s : ℕ, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : I) (c : Par), c ∈ V →
      let result := orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
        (fun c ↦ demodulatedL2Operator (lam i) (φ i c)
          ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
          (capped i o) (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) c
      MemVectorFourierSobolev (s:ℝ) result ∧
        vectorFourierSobolevNorm (s:ℝ) result ≤
          C * lam i ^ (-(o.val:ℤ)) * A₀ i * K i ^ (s+ps.length-Rsource) := by
  intro c z U O D Z KP Ksigned β π hmaskBox hcone hsel hcoverage htimePlateau heχp
  obtain ⟨SN,hSN,hnearBound⟩ := physical_history_reserved_annular_envelopes_for_supplied_cutoff
    (I := I) negative T χp f p hprotect hbufferTarget hsrcBuffer hε hεroot hεbuffer
    hAp hg hRad htime htimeε hsrctime hphysical hV hVc hVcov ha₀ hB₀ hm hMfreq
    InvBound hInv output ho hoc hos threshold hthreshold angular hangPlateau Damp hDamp
    Gref hr hrR hR ext hextcenter hextradius hBband hStar hRstar hcompression hreserve
    horder basis hν hν1 hmaskBox hcone hsel hcoverage htimePlateau heχp
  obtain ⟨ST,hST,htailBound⟩ := exists_physical_history_retarded_complement_envelopes
    (I := I) (Rad := Rad) T f p hprotect hbufferTarget hsrcBuffer hε hεroot hεbuffer
    hAp hg htimeε hsrctime hphysical hV hVc hVcov ha₀ hB₀ hm hm1 hMfreq
    output ho hoc hos hob threshold hthreshold angular hang hangPlateau Damp hDamp
    χout χsource hχsource base cost hlocalout hlocalin Gref hr hrR hR ext
    hextcenter hextradius hBband hStar (by omega) hRstar hreserve horder hν hν1 χp
    heχp hmaskBox hcone hcoverage htimePlateau
  refine ⟨max SN ST,hSN.trans (le_max_left _ _),?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L sourcePhase h Φ chart G hbuffer hsm hdiff hnear hphase hsourceTime
    Fs matrix Ws hFs hmatrix hsupport hGsolver hGres hbudget
    hsourceBand hradial Op hOp e Mo Mi capped
    κ raw hraw hκ hstat hHess hsegments lam K A₀ hlam hLK hscale hA₀
    S hS hSU a ha has Csource hCsource hfourier φ hprimary o s ps hps
  have hSNi i : SN ≤ R₀ i := (le_max_left _ _).trans (hR₀ i)
  have hSTi i : ST ≤ R₀ i := (le_max_right _ _).trans (hR₀ i)
  have hL i : 1 ≤ L i := one_le_currentCoefficientScale (by linarith [hSNi i]) (n i)
  have hK i : 1 ≤ K i := (hL i).trans (hLK i)
  have hfourierCoarse : ∀ i b, b ∈ V → ∀ l (w : Fin l → Par),
      (∀ j, ‖w j‖ ≤ 1) → ∀ t : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) b w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (t : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (t : ℝ) (hm.toLp f) ≤ Csource l t*A₀ i*K i^(t+l) := by
    intro i b hb l w hw t
    obtain ⟨hm,ht,hb⟩ := hfourier i b hb l w hw t
    refine ⟨hm,ht,hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hK i) (Nat.sub_le _ _))
      (mul_nonneg (hCsource l t) (hA₀ i))
  let φtail := fun i b y ↦ if negative then
    -(χp (y,b)*T.fullSourcePhaseInCoordinates c.index (Q i) y b)
    else χp (y,b)*T.fullSourcePhaseInCoordinates c.index (Q i) y b
  have hφeq : φtail = φ := by
    funext i b y
    cases negative <;> simp only [φtail,φ,sourcePhase,Bool.false_eq_true,ite_false,ite_true,
      PatchQuantitativeFamily.negativeFullSourcePhaseInCoordinates,mul_neg]
  have hprimaryTail : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φtail i q.2 q.1) := by
    simpa only [hφeq] using hprimary
  have htail := htailBound R₀ n u ell hSTi hu Q hQ h Φ chart G hbuffer hsm hdiff hnear
    hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hradial
    Op hOp negative lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hfourierCoarse
    hprimaryTail o
  let outTail := fun i b ↦ demodulatedL2Operator (lam i) (φtail i b)
    ((hprimaryTail i).continuous.comp (continuous_id.prodMk continuous_const))
    (capped i o) (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b)) -
    annularEnvelopeIntegral (3*c.maskRadius/4)
      (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (if o=0 then Ws i 0+Ws i 1 else Ws i 2)
      (endpointOutputMask f p output) (chartInputMask f p) β π (lam i) (φtail i b)
      ((hprimaryTail i).continuous.comp (continuous_id.prodMk continuous_const))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b))
  change (∀ i, ContDiffOn ℝ ∞ (outTail i) V) ∧
      (∀ (s : ℝ) (k : ℕ) (Qaccuracy : ℝ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ i b, b ∈ V → ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
          MemVectorFourierSobolev s (iteratedFDeriv ℝ k (outTail i) b v) ∧
          vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (outTail i) b v) ≤
            C*A₀ i*lam i^(-Qaccuracy)) at htail
  dsimp only [outTail] at htail
  simp only [hφeq] at htail
  let full := fun i b ↦ demodulatedL2Operator (lam i) (φ i b)
    ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
    (capped i o) (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b))
  let near := fun i b ↦ annularEnvelopeIntegral (3*c.maskRadius/4)
    (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (if o=0 then Ws i 0+Ws i 1 else Ws i 2)
    (endpointOutputMask f p output) (chartInputMask f p) β π (lam i) (φ i b)
    ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
    (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b))
  let tail := fun i b ↦ full i b - near i b
  have hX : IsCompact (Prod.fst '' tsupport χp) := hcχp.image continuous_fst
  have hφsupport i b : tsupport (φ i b) ⊆ Prod.fst '' tsupport χp := by
    apply closure_minimal ?_ hX.isClosed
    intro y hy
    have hχ : χp (y,b) ≠ 0 := by
      intro he
      apply hy
      change χp (y,b)*sourcePhase i y b = 0
      rw [he,zero_mul]
    exact ⟨(y,b),subset_tsupport χp hχ,rfl⟩
  have hfullSmooth i : ContDiffOn ℝ ∞ (full i) V := by
    exact FixedDomainInverse.FiniteResidualWordProfiles.contDiffOn_demodulated_supported_operator
      hV hS hX (a i) (ha i) (has i) (lam i) (φ i)
      ((hprimary i).comp (contDiff_snd.prodMk contDiff_fst))
      (fun b _ ↦ hφsupport i b) (capped i o)
  have hnearSmooth i : ContDiffOn ℝ ∞ (near i) V := by
    apply ((hfullSmooth i).sub (htail.1 i)).congr
    intro b _
    change near i b = full i b - (full i b - near i b)
    abel
  have hnb := hnearBound R₀ n u ell hSNi hu Q hQ h Φ chart G hbuffer hsm hdiff hnear
    hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget
    κ hraw hκ hstat hHess hsegments lam K A₀ hlam hLK hscale hA₀
    S hS hSU a ha has Csource hfourier hprimary o
  have hrestored := FixedDomainInverse.FiniteResidualEnvelopes.ordered_reserved_bounds_of_annular_remainder
    full near tail hV (fun i b _ ↦ by dsimp [tail]; abel)
    hnearSmooth htail.1 lam A₀ K (-(o.val:ℤ)) Rsource hlam hA₀ hK
    (fun ps hps s ↦ hnb s ps hps) htail.2
  exact hrestored.2 ps hps s

end JanetCartan.PhysicalPrimary
