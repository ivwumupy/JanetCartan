module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicWholeImage
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicPhase
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAmplitude
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAnnular
public import JanetCartan.Iteration.PhysicalPrimary.IncidencePhase

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.WholeImageProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CompletePhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CoveredAmplitudeProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.CoveredAnnularProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedRepresentativeGraphs
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.PhysicalIncidenceEnvelopes
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceInterval
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.SmoothRepresentative

/-!
# Full-source envelopes of the original selected history operators

Construct the phase, complete-frequency and annular amplitude profiles, whole-image
geometry and graph realizations from their original producers. The physical
full-source theorem then applies to both original characteristic orders and
literal orientations. Its remaining stationary and source certificates must
still be instantiated on the original pre-reference family and primary source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalPrimary
open ResponseTransfer ResponseTransfer.RetainedCharacteristicEnvelopes
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

/-- Apply the full-source envelope to the original selected history matrices.
All primary/joint phase grades, complete and annular amplitude grades, graph
realizations, and whole-image geometry are constructed from the existing
history producers and original chart/symbol certificates. The remaining
stationary and gradient inputs are the exact outputs of the pre-reference
selector on this SAME family. Source Fourier inputs have the exact signature
of `exists_localized_retained_reducedSource_physical_fourier_profiles`.
Their original-source and finite-constructor instantiations remain explicit
obligations; this theorem does not select a second family or an inverse
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_physical_history_selected_operator_envelopes
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
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (angular : Euclidean d → ℝ) (hang : ContDiff ℝ ∞ angular)
    (hangPlateau : ∀ ξ ∈ tsupport (selectedEndpointMultiplier f p threshold),
      conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (Damp : ℕ → ℝ) (hDamp : ∀ j, 0 ≤ Damp j)
    {ra rb : ℝ}
    (Gref : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (h12 : 12 ≤ rStar)
    (hRstar : fullLowReserve (d+1)+2 < Rstar) (hreserve : Rstar+10 ≤ rStar)
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
            ((if adj then fun u ↦ ∫ t in Icc 0 (3*(f.chart p).maskRadius/4),
                (elapsedGraph (fun t s y ξ ↦ G q.1 (t,(s,(y,ξ))))
                  (if o=0 then Ws q.1 0+Ws q.1 1 else Ws q.1 2)
                  (endpointOutputMask f p output) (chartInputMask f p) β t).adjoint u
              else elapsedGraphIntegral (3*(f.chart p).maskRadius/4)
                (fun t s y ξ ↦ G q.1 (t,(s,(y,ξ))))
                (if o=0 then Ws q.1 0+Ws q.1 1 else Ws q.1 2)
                (endpointOutputMask f p output) (chartInputMask f p) β)
              (carrierMultiplication (lam q.1) (φ q.1 c)
                ((hprimary q.1).continuous.comp (continuous_id.prodMk continuous_const))
                (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))))) q.2)
        (fun q ↦ lam q.1^(-(o.val : ℤ))*A₀ q.1*K q.1^ps.length) (fun q ↦ K q.1) := by
  intro c z U O D Z KP Ksigned β Dn hmaskBox hcone hsel hcoverage htimePlateau
  have hsrcε : c.maskRadius ≤ ε := hsrctime.trans htimeε
  have hεtarget : 4*ε ≤ c.targetRadius := by linarith
  obtain ⟨hO,hOc⟩ := retainedOpenAnnularFrequencyCarrier_open_convex c.radialSection z.2.2
    (ε/2) aperture g Rad
  have hOK : IsCompact (closure O) :=
    (isCompact_closedBall (0 : E) Rad).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ h ↦ ball_subset_closedBall h.1) isClosed_closedBall)
  obtain ⟨χp,hχp,hcχp,heχp,SP,hSP,Bprimary,Aphase,hBprimary,hAphase,hprimaryProfiles⟩ :=
    exists_physical_history_protected_incidence_profiles T c hprotect hε hεroot hεtarget
      hAp hg hphysical hVc hVcov Gref hr hrR hR ext hextcenter hextradius hBband hStar
      (by omega : Rstar+3 ≤ rStar) horder hO hOc hOK
  obtain ⟨SB,hSB,Bphase,hBphase,hphaseProfiles⟩ :=
    exists_history_selected_complete_phase_profiles c hε hεtarget hAp.le hsrcε
      Gref hr hrR hR ext hextcenter hextradius hBband hStar horder
  obtain ⟨SA,hSA,Bamp,hBamp,hampProfiles⟩ :=
    exists_history_selected_amplitude_profiles f p Gref hr hrR hR ext hextcenter hextradius
      hBband h12 horder hε (by linarith : ε ≤ c.bufferRadius/2) hsrcε threshold Damp hDamp hcoverage
  let aSel := a₀/(2*Mfreq)
  let bSel := 2*B₀/m
  have haSel : 0 < aSel := div_pos ha₀ (by positivity)
  have hbSel : 0 < bSel := div_pos (by positivity) hm
  let π : E → ℂ := fun ξ ↦ annularSelector aSel bSel haSel hbSel ξ
  have hπ : ContDiff ℝ ∞ π := Complex.ofRealCLM.contDiff.comp (contDiff_annularSelector ..)
  obtain ⟨SN,hSN,Aamp,hAamp,hannProfiles⟩ :=
    exists_physical_history_incidence_annular_profiles f p Gref hr hrR hR ext
      hextcenter hextradius hBband hreserve horder hsrcBuffer hε hεbuffer hAp hg hRad hVc
      output ho threshold hthreshold π hπ Damp hDamp hcoverage
  obtain ⟨SW,hSW,graphGap,hgraphGap,bandLo,hbandLo,bandHi,hbands,Mgraph,hMg,
      Ggraph,hGg,cgraph,hcgraph,growth,hgrowth,hwholeProfiles⟩ :=
    exists_physical_history_selected_wholeImage_geometry c hε hεtarget hAp.le hsrcε
      Gref hr hrR hR ext hextcenter hextradius hBband hStar hRstar
      (by omega : Rstar+5 ≤ rStar) horder
  have hstrict : 4*ε < c.targetRadius := by linarith [c.bufferRadius_pos]
  obtain ⟨δ,hδ,hδhalf,hδg,χg,hχg,hcχg,hsχg,heg,hrep⟩ :=
    SmoothRepresentative.exists_common_smooth_representative c.radialSection
      (isCompact_closedBall (z.1,z) (4*ε)) isOpen_ball (closedBall_subset_ball hstrict)
      (by norm_num : (0 : ℝ) < 1/2) (div_pos hg (by positivity : 0 < 1+‖c.radialSection‖))
  let S₀ := max SP (max SB (max SA (max SN SW)))
  refine ⟨χp,hχp,hcχp,heχp,S₀,hSP.trans (le_max_left _ _),?_⟩
  intro R₀ n u ell hR₀ hu Q hQ B L h Φ chart G hbuffer hsm hdiff hnear hphase hsourceTime
    Fs matrix Ws hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hradial
    κ raw hraw hκ hstat hHess hsegments lam K A₀ hlam hLK hscale hA₀
    S hS hSU a ha has Csource hfourier φ
  have hSPi i : SP ≤ R₀ i := (le_max_left _ _).trans (hR₀ i)
  have hSBi i : SB ≤ R₀ i := (le_max_left _ _).trans ((le_max_right _ _).trans (hR₀ i))
  have hSAi i : SA ≤ R₀ i := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (hR₀ i)))
  have hSNi i : SN ≤ R₀ i := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hR₀ i))))
  have hSWi i : SW ≤ R₀ i := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hR₀ i))))
  have hL i : 1 ≤ L i := one_le_currentCoefficientScale (by linarith [hSPi i]) (n i)
  have hp i := (hprimaryProfiles (Q i)).2.2 (R₀ i) (hSPi i) (n i) (u i) (ell i) (hu i) (hQ i)
  have hprimary i : ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1) :=
    (hprimaryProfiles (Q i)).1
  refine ⟨hprimary,?_⟩
  intro o adj ps hps
  -- All selected history profile and graph inputs are instantiated below.
  have hβD : tsupport β ⊆ Dn := by
    intro ξ hξ
    have hcan := RegularSector.FiniteEvolution.PhysicalCutoff.tsupport_complex_physical_dilatedConicMask_subset
      (f.angularMask p) c.index (zero_lt_one.trans_le hthreshold) hξ
    have hr : ξ ∈ tsupport (dilatedConicMask (f.angularMask p ∘ physicalCoordinates c.index) threshold) :=
      tsupport_comp_subset Complex.ofReal_zero _ hcan
    refine ⟨dilatedConicMask_tsupport_subset_fullAngularCone c.radialSection z _ _ _ hcone
      (zero_lt_one.trans_le hthreshold) hr,?_⟩
    have he := (hangPlateau ξ hξ).eq_of_nhds
    have hn : conicMask angular (spatialPart ξ) ≠ 0 := by rw [he]; norm_num
    have hh := (conicMask_tsupport_subset angular (subset_tsupport _ hn)).1
    change (1/2 : ℝ) < ‖spatialPart ξ‖
    linarith
  obtain ⟨hχout,hcχout,_⟩ := endpointOutputMask_properties f p ho hoc hos
  obtain ⟨_,hχsource,_,hcχsource,_⟩ := chartPhysicalMasks_properties f p
  have hXU := selected_common_physical_masks_subset_stationary_box f p z ε hmaskBox output hos
  have hW i k : ContDiff ℝ ∞ (jointAmplitude (Ws i k)) :=
    (hmatrix i k).comp (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  let W := fun i ↦ if o=0 then Ws i 0+Ws i 1 else Ws i 2
  have hWo i : ContDiff ℝ ∞ (jointAmplitude (W i)) := by
    by_cases h : o=0
    · simp only [W,ite_eq_left h]
      change ContDiff ℝ ∞ (jointAmplitude (Ws i 0) + jointAmplitude (Ws i 1))
      exact (hW i 0).add (hW i 1)
    · simpa only [W,ite_eq_right h] using hW i 2
  let Ψ := fun i ↦ SmoothRepresentative.curriedRepresentative c.radialSection δ hδ χg (twoTimePhase (chart i))
  have hΨ i : ContDiff ℝ ∞ (jointPhase (Ψ i)) :=
    (hrep (chart i) (ball_subset_closedBall.trans (hbuffer i)) (hsm i)).1.comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
        (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  have hgph i := exists_selected_physical_representative_graph_realizations f p hbufferTarget hsrcBuffer
    hε hsrcε output ho hoc hos threshold hthreshold angular hang hangPlateau hmaskBox hβD
    δ hδ hδhalf χg heg (Q i).1 (B i) (h i) (Φ i) (chart i)
    (hbuffer i) (hsm i) (hdiff i) (hnear i) (hphase i) (hsourceTime i)
    (hFs i) (hmatrix i) (hsupport i)
  choose Creg hgraphs using hgph
  let η := fun i t ↦ wholeImageInverse (elapsedPhase (curriedPhase c.radialSection (chart i)) t) Dn
  let J := fun i t ↦ averagedJacobian (elapsedPhase (curriedPhase c.radialSection (chart i)) t)
  let Rcell := 1+|z.1|+‖z.2.1‖+ε
  have hRcell : 0 < Rcell := by dsimp [Rcell]; positivity
  have hbox : ∀ y ∈ U, ‖y‖ ≤ Rcell := by
    intro y hy
    have hn := norm_le_on_elapsedPhysicalBox hy
    dsimp only [Rcell]
    linarith
  let ac := fun i c y ↦ a i (y,c)
  have ha' i : ContDiffOn ℝ ∞ (Function.uncurry (ac i)) (V ×ˢ univ) :=
    ((ha i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have has' i c (_hc : c ∈ V) : tsupport (ac i c) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra hys
    exact hy (has i (y,c) hys)
  have hmem i c (hc : c ∈ V) l (w : Fin l → Par) (hw : ∀ j, ‖w j‖ ≤ 1) (s : ℕ) :=
    (hfourier i c hc l w hw s).choose_spec.1
  have hsob i c (hc : c ∈ V) l (w : Fin l → Par) (hw : ∀ j, ‖w j‖ ≤ 1) (s : ℕ) :=
    (hfourier i c hc l w hw s).choose_spec.2
  refine fullSource_physical_incidence_solver_residual_envelopes T c.index c.radialSection z
    hε hAp hg htime htimeε c.maskRadius_pos.le hsrctime hδ hδg hδhalf
    hν hν1 ha₀ hB₀ hm hm1 hMfreq hRcell hgraphGap hgrowth.le Mgraph Ggraph cgraph hcgraph
    basis Rstar hRstar hV hVc hS (endpointOutputMask f p output) (chartInputMask f p)
    hχout hχsource hcχout hcχsource c.timeMask htimePlateau (f.angularMask p)
    (f.angularMask_smooth p) (f.angularMask_range p) hcone threshold (zero_lt_one.trans_le hthreshold)
    χg heg χp Bphase Bprimary Bamp Aphase Aamp Csource hBphase hBprimary hBamp hAphase hAamp
    InvBound hInv bandLo bandHi Q chart G matrix hGsolver hGres κ η J lam L K A₀ hlam hL hLK hscale hA₀
    ac ha has ha' has' o (fun i ↦ Creg i o) hO hOc hOK hsel hSU hXU hβD hbox heχp hprimary
    (fun i ↦ (hp i).1) hΨ hWo ?_ ?_ ?_ ?_ (fun i ↦ hgraphs i o) ?_
    hraw hκ hstat hHess hsegments ?_ ?_ hmem hsob adj ps hps
  · intro i t ht ξ hξ j y hy
    simpa only [L] using hphaseProfiles (R₀ i) (hSBi i) (n i) (u i) (ell i) (hu i)
      (chart i) (hbuffer i) (hsm i) (by simpa only [← hQ i] using hphase i)
      δ hδ hδhalf χg heg t ht ξ (hβD hξ) j y hy
  · intro i t ht ξ hξ j y hy
    simpa only [← hQ i,fullElapsedPhysicalFactor,matrix,Fs,Ws,selectedConicAmplitude,B,L,c] using hampProfiles (R₀ i) (hSAi i) (n i) (u i) (ell i) (hu i)
      (Φ i) (chart i) angular (by simpa only [← hQ i] using hmatrix i)
      (by simpa only [← hQ i] using hbudget i) t ht ξ hξ j y hy o
  · intro i c hc y hy
    exact hsourceBand i (y,c) ⟨subset_closure
      (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hy)),subset_closure hc⟩
  · intro i t ht ξ hξ y hy
    have he := (SmoothRepresentative.elapsed_representative_eventuallyEq c.radialSection (chart i)
      hδ heg (capped_elapsedPoint_mem_phase_plateau c.radialSection z hε hsrcε ht hy (hβD hξ))
      (hδhalf.trans (hβD hξ).2.le)).comp_tendsto
        (continuous_id.prodMk continuous_const).continuousAt
    have hf : (fun v ↦ elapsedPhase (Ψ i) t v ξ) =ᶠ[𝓝 y]
        (fun v ↦ elapsedPhase (curriedPhase c.radialSection (chart i)) t v ξ) := he
    rw [hf.fderiv_eq]
    exact hradial i t ⟨ht.1,by linarith [ht.2]⟩ y hy ξ (hβD hξ)
  · intro i t ht
    simpa only [← hQ i] using hwholeProfiles (R₀ i) (hSWi i) (n i) (u i) (ell i) (hu i)
      (h i) (Φ i) (chart i) (hbuffer i) (hsm i) (hdiff i) (hnear i)
      (by simpa only [← hQ i] using hphase i) δ hδ hδhalf χg heg t ht
  · intro i rev j t v hv
    exact ((hp i).2 (chart i) (hbuffer i) (hsm i) (hphase i) rev j).2 t v hv
  · intro i rev t ht j v hv
    have hj := hannProfiles (R₀ i) (hSNi i) (n i) (u i) (ell i) (hu i)
      (Φ i) (chart i) angular (by simpa only [← hQ i] using hmatrix i)
      (by simpa only [← hQ i] using hbudget i) t ht (lam i) (hlam i) o rev j v hv
    simp only [← hQ i] at hj
    convert hj using 1
    rfl

end JanetCartan.PhysicalPrimary

