module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedHistoryEnvelopes
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedOperatorActions

/-!
# Arbitrary supported envelopes through the selected characteristic operator

The datum is not required to be an original primary strain: the next finite
residual word supplies another smooth supported envelope. Apply the existing
history calculus to that datum and identify its integral with the same supplied
operator using its retained test-action certificate. Both actual orders and
literal adjoints retain the full elapsed interval and the prescribed windows.
No new operator, phase or inverse is selected here.

Consumers: the characteristic-letter induction for
`app:ch_response:eq:response-graded-reduced`; the initial primary datum is the
`app:ch_response:eq:response-graded-source` instance at depth zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open JanetCartan.ResponseTransfer JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
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

/-- The original once-capped selected operators act on arbitrary supported
joint envelopes with the same sharp scale. The input Fourier bounds concern
only the supplied datum; all phase, amplitude, kernel realization and operator
bounds are applied from the original retained history certificates. This is
the one-characteristic-letter producer used at every finite residual depth
(`app:ch_response:eq:fixed-factor-transfer`). The `adj` flag means the literal
adjoint; whole conjugation still uses the opposite-carrier transfer. -/
theorem exists_selected_history_capped_source_envelopes
    (T : PatchQuantitativeFamily P Uref hUref)
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
    {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (h12 : 12 ≤ rStar)
    (hRstar : fullLowReserve (d+1)+2 < Rstar) (hreserve : Rstar+10 ≤ rStar)
    (horder : displacementLoss (d+1) +
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
    let Dn := retainedFrequencyDomain c.radialSection z ε aperture (1/2)
    MapsTo (primaryCoordinateChange c.index) (tsupport f.inputMask ∪ tsupport f.outputMask) U →
    (tsupport (f.angularMask p ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone c.radialSection z.2.2 (ε/4) (aperture/2)) →
    (retainedAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture
      (retainedSelectorGap z.2.2 (ε/2) aperture (a₀/(2*Mfreq))) (2*(2*B₀/m)) ⊆ O) →
    RetainedConstruction.DiagonalFrequencyCoverage c.radialSection z.2.2
      (c.bufferRadius/2) ra rb β →
    (∀ y, endpointOutputMask f p output y ≠ 0 → c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1)) →
    ∃ χp : E × Par → ℝ, ContDiff ℝ ∞ χp ∧ HasCompactSupport χp ∧
      (∀ q ∈ KP, χp =ᶠ[𝓝 q] (fun _ ↦ 1)) ∧
    ∃ S₀ : ℝ, 2 ≤ S₀ ∧
    ∀ (R₀ : I → ℝ) (n : I → ℕ)
      (u : ∀ i, Fin (n i) → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
      (ell : ∀ i, Fin (n i) → ℕ), (∀ i, S₀ ≤ R₀ i) →
      (∀ i, IsAdmissibleHistory (R₀ i) kMin (u i) (ell i)) →
    ∀ Q : I → {Q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q Uref ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold},
      (∀ i, (Q i).1 = extendedProjectedStress ext (finiteHistoryMap Gref.map (u i))) →
    let B := fun i ↦ reducedZerothProjection (d+1) ∘
      extendedReducedCoefficients ext (fun _ _ ↦ 0) (finiteHistoryMap Gref.map (u i))
    let L := fun i ↦ currentCoefficientScale (R₀ i) (n i)
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
    (∀ i t, t ∈ Icc 0 ε → ∀ y ∈ U, ∀ ξ ∈ Dn,
      m*‖ξ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase c.radialSection (chart i)) t v ξ) y‖ ∧
      ‖fderiv ℝ (fun v ↦ elapsedPhase (curriedPhase c.radialSection (chart i)) t v ξ) y‖ ≤ Mfreq*‖ξ‖) →
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
    ∀ κ : I → Bool → (ℝ × (E × Par)) → CW,
    let raw := fun i adj ↦ fullSourceJointPhase adj (curriedPhase c.radialSection (chart i))
      (T.fullSourcePhaseInCoordinates c.index (Q i))
    (∀ i adj, ContDiffOn ℝ ∞ (raw i adj) (Z ×ˢ D)) →
    (∀ i adj, ContDiffOn ℝ ∞ (κ i adj) Z) →
    (∀ i adj q, q ∈ Z → κ i adj q ∈ D ∧
      gradient (fun w ↦ raw i adj (q,w)) (κ i adj q) = 0 ∧ raw i adj (q,κ i adj q) = 0) →
    (∀ i adj q, q ∈ Z → ∀ w ∈ closure D,
      let phase := fun b w ↦ raw i adj ((q.1,b),w)
      IsUnit (averagedPhaseHessian phase (fun b ↦ κ i adj (q.1,b)) q.2 w) ∧
        ‖Ring.inverse (averagedPhaseHessian phase (fun b ↦ κ i adj (q.1,b)) q.2 w)‖ ≤ InvBound) →
    (∀ i adj q, q ∈ Z → ∀ w ∈ closure D,
      ∀ t ∈ uIcc (0 : ℝ) q.1, ∀ a ∈ Icc (0 : ℝ) 1,
        ((t,q.2),κ i adj q + a • (w-κ i adj q)) ∈ Ksigned) →
    ∀ (lam K A₀ : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ A₀ i) →
    ∀ (S : Set E) (hS : IsCompact S), S ⊆ U →
    ∀ (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ),
    (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A₀ i*K i^(s+l)) →
    let φ := fun i c y ↦ χp (y,c)*T.fullSourcePhaseInCoordinates (f.chart p).index (Q i) y c
    ∃ hprimary : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1),
    ∀ o : Fin 2, ∀ adj : Bool, ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile (vectorFourierSobolevScale (d := d+1) (I := Fin (d+1)))
        (fun q : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
          (fun c ↦ carrierMultiplication (-(lam q.1)) (φ q.1 c)
            ((hprimary q.1).continuous.comp (continuous_id.prodMk continuous_const))
            ((if adj then (capped q.1 o).adjoint else capped q.1 o)
              (carrierMultiplication (lam q.1) (φ q.1 c)
                ((hprimary q.1).continuous.comp (continuous_id.prodMk continuous_const))
                (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))))) q.2)
        (fun q ↦ lam q.1^(-(o.val : ℤ))*A₀ q.1*K q.1^ps.length) (fun q ↦ K q.1) := by
  intro c z U O D Z KP Ksigned β Dn hmaskBox hcone hsel hcoverage htimePlateau
  obtain ⟨χp,hχp,hcχp,heχp,S₀,hS₀,henvelope⟩ := exists_selected_history_operator_envelopes
    (I := I) T f p hprotect hbufferTarget hsrcBuffer hε hεroot hεbuffer hAp hg hRad
      htime htimeε hsrctime hphysical hV hVc hVcov ha₀ hB₀ hm hm1 hMfreq InvBound hInv
      output ho hoc hos threshold hthreshold angular hang hangPlateau Damp hDamp
      Gref hr hrR hR ext hextcenter hextradius hStar h12 hRstar hreserve horder basis hν hν1
      hmaskBox hcone hsel hcoverage htimePlateau
  refine ⟨χp,hχp,hcχp,heχp,S₀,hS₀,?_⟩
  intro R₀ stage u ell hR₀ hu Q hQ B L h Φ chart G hbuffer hsm hdiff hnear hphase hsourceTime
    Fs matrix Ws hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hradial
    Op hOp e Mo Mi capped κ raw hraw hκ hstat hHess hsegments
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hfourier φ
  have hactions i := selected_once_capped_operator_actions f p hbufferTarget hsrcBuffer
    output ho hoc hos hob threshold hthreshold angular hang hangPlateau
    (Q i).1 (B i) (h i) (Φ i) (chart i) (hbuffer i) (hsm i) (hdiff i) (hnear i) (hphase i)
    (hsourceTime i) (hFs i) (hmatrix i) (hsupport i) (G i) (hGsolver i) (hGres i)
    χout χsource hχsource base cost (Op i) (hOp i) hlocalout hlocalin
  obtain ⟨hprimary,hprofile⟩ := henvelope R₀ stage u ell hR₀ hu Q hQ h Φ chart G
    hbuffer hsm hdiff hnear hphase hsourceTime hFs hmatrix hsupport hGsolver hGres hbudget
    hsourceBand hradial κ hraw hκ hstat hHess hsegments
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hfourier
  refine ⟨hprimary,?_⟩
  intro o adj ps hps
  have hforward i o v : capped i o v = elapsedGraphIntegral (3*c.maskRadius/4)
      (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (if o=0 then Ws i 0+Ws i 1 else Ws i 2)
      (endpointOutputMask f p output) (chartInputMask f p) β v := (hactions i).2.1 o v
  have hadjoint i o v : (capped i o).adjoint v = ∫ t in Icc 0 (3*c.maskRadius/4),
      (elapsedGraph (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (if o=0 then Ws i 0+Ws i 1 else Ws i 2)
        (endpointOutputMask f p output) (chartInputMask f p) β t).adjoint v := (hactions i).2.2 o v
  cases adj
  · simpa only [Bool.false_eq_true,ite_false,hforward] using hprofile o false ps hps
  · simpa only [ite_true,hadjoint] using hprofile o true ps hps

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
