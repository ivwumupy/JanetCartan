module

public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicOperators

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.SelectedCharacteristic
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.InactiveFullSourceEnvelopes
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointInactiveSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SelectedOperatorActions

/-!
# Inactive physical-history letters with the supplied original source cutoff

The history producers supply the actual source phase, full graph phase,
normalized amplitudes and canonical graph regularizations. Their complete
inactive kernel estimate applies to the original once-capped selected solver,
full retarded residual, and both literal adjoints. The source-sign flag and
literal-adjoint flag are independent. The supplied original source cutoff and
phase are preserved, including during demodulation.

The forward angular gap comes from the supplied-incidence cutoff. In the
adjoint case the actual graph momentum replaces the bare frequency: its
geometric producer is original-root/flow stability near the cube coefficients.
This producer remains an explicit parent instantiation obligation. All analytic
kernel and operator estimates here are derived from the actual primitive jets.
Consumer: the active/inactive split in the finite measured residual words
(`app:ch_response:eq:response-whole-source-partition`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalPrimary
open CharacteristicAdjointInactive
open FixedDomainInverse FixedDomainInverse.FiniteResidualEnvelopes
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

/-- The SAME selected solver, full retarded residual and their literal adjoints have arbitrary inactive
precision for either original source sign and the supplied original phase cutoff.
The adjoint angular condition uses the actual transported graph momentum; its
producer is original-root/flow stability, not the forward gap. The primitive
jet profiles precede the history family; the uniform estimates do not use the
original low operator norm. The actual fixed parameter support and its
corresponding angular gap are retained
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_physical_history_inactive_capped_envelopes_for_supplied_cutoff
    (adj : Bool)
    (T : PatchQuantitativeFamily P Uref hUref) (χp : E × Par → ℝ)
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K₀ Mcap) (p : f.centers)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate (f.chart p) evolutionTime speedGap rootSize rootCost)
    (hbufferTarget : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcBuffer : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {ε aperture g Rad timeRadius : ℝ} (hε : 0 < ε)
    (hεroot : ε ≤ (f.chart p).rootRadius) (hεbuffer : ε ≤ (f.chart p).bufferRadius/8)
    (hAp : 0 < aperture) (hg : 0 < g)
    (htimeε : timeRadius ≤ ε)
    (hsrctime : (f.chart p).maskRadius ≤ timeRadius)
    (hphysical : closedBall x RQ ⊆ ball 0 T.physicalRadius)
    {V : Set Par} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVcov : ∀ q ∈ closure V,
      q.2 ∈ ball (FullPhaseCharts.ActualPhase.covectorCenter T) T.family.radius)
    {a₀ B₀ m Mfreq : ℝ} (ha₀ : 0 < a₀) (hm : 0 < m) (hm1 : m ≤ 1)
    (hMfreq : 0 ≤ Mfreq)
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
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (h12 : 12 ≤ rStar)
    (hRstar : fullLowReserve (d+1)+2 < Rstar) (hreserve : Rstar+10 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    let c := f.chart p
    let z : RootState (Euclidean d) := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2,(coordinateSplit c.index p.val.val).2))
    let U := elapsedPhysicalBox z (ε/2)
    let KP := closure (elapsedPhysicalBox z ε) ×ˢ closure V
    let β := selectedEndpointMultiplier f p threshold
    MapsTo (primaryCoordinateChange c.index) (tsupport f.inputMask ∪ tsupport f.outputMask) U →
    (tsupport (f.angularMask p ∘ physicalCoordinates c.index) ∩ sphere (0 : E) 1 ⊆
      fullAngularCone c.radialSection z.2.2 (ε/4) (aperture/2)) →
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
    (∀ i t, t ∈ Icc 0 c.maskRadius → ∀ y ∈ U,
      ∀ ξ ∈ retainedFrequencyDomain c.radialSection z ε aperture (1/2),
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
    ∀ (negative : Bool) (P₀ : Set Par), IsClosed P₀ →
    ∀ gap : ℝ, 0 < gap →
    let rawSource := fun i c y ↦ if negative then
      -(T.fullSourcePhaseInCoordinates (f.chart p).index (Q i) y c)
      else T.fullSourcePhaseInCoordinates (f.chart p).index (Q i) y c
    (∀ i b, b ∈ V → b ∈ P₀ → ∀ t ∈ Icc 0 (3*c.maskRadius/4),
      ∀ y ∈ U, ∀ ξ ∈ tsupport β,
      gap ≤ dist (NormedSpace.normalize (gradient (rawSource i b) y))
        (if adj then NormedSpace.normalize (gradient
          (fun v ↦ elapsedPhase (curriedPhase c.radialSection (chart i)) t v ξ) y)
        else NormedSpace.normalize ξ)) →
    ∀ (lam K A₀ : I → ℝ), (∀ i, 1 ≤ lam i) → (∀ i, L i ≤ K i) →
      (∀ i, K i ≤ lam i^(1-ν)) → (∀ i, 0 ≤ A₀ i) →
    ∀ (S : Set E) (hS : IsCompact S), S ⊆ U →
    ∀ (a : I → E × Par → Fibre) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ),
    (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A₀ i*K i^(s+l)) →
    (∀ i c, c ∉ P₀ → ∀ y, a i (y,c) = 0) →
    let φ := fun i c y ↦ if negative then
      -(χp (y,c)*T.fullSourcePhaseInCoordinates (f.chart p).index (Q i) y c)
      else χp (y,c)*T.fullSourcePhaseInCoordinates (f.chart p).index (Q i) y c
    ∀ hprimary : ∀ i, ContDiff ℝ ∞ (fun q : E × Par ↦ φ i q.2 q.1),
    ∀ o : Fin 2,
      let out := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
        ((hprimary i).continuous.comp (continuous_id.prodMk continuous_const))
        (if adj then (capped i o).adjoint else capped i o) (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
      (∀ i, ContDiffOn ℝ ∞ (out i) V) ∧
      ∀ (s : ℝ) (k : ℕ) (Qaccuracy : ℝ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ i c, c ∈ V → ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
          MemVectorFourierSobolev s (iteratedFDeriv ℝ k (out i) c v) ∧
          vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (out i) c v) ≤
            C*A₀ i*lam i^(-Qaccuracy) := by
  intro c z U KP β hmaskBox hcone hcoverage htimePlateau heχp
  let O := retainedOpenAnnularFrequencyCarrier c.radialSection z.2.2 (ε/2) aperture g Rad
  let Dn := retainedFrequencyDomain c.radialSection z ε aperture (1/2)
  have hsrcε : c.maskRadius ≤ ε := hsrctime.trans htimeε
  have hεtarget : 4*ε ≤ c.targetRadius := by linarith
  obtain ⟨hO,hOc⟩ := retainedOpenAnnularFrequencyCarrier_open_convex c.radialSection z.2.2
    (ε/2) aperture g Rad
  have hOK : IsCompact (closure O) :=
    (isCompact_closedBall (0 : E) Rad).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ h ↦ ball_subset_closedBall h.1) isClosed_closedBall)
  obtain ⟨χp₀,_hχp₀,_hcχp₀,heχp₀,SP,hSP,Bprimary,Aphase,hBprimary,hAphase,hprimaryProfiles⟩ :=
    exists_physical_history_protected_incidence_profiles T c hprotect hε hεroot hεtarget
      hAp hg hphysical hVc hVcov Gref hr hrR hR ext hextcenter hextradius hBband hStar
      (by omega : Rstar+3 ≤ rStar) horder hO hOc hOK
  obtain ⟨SB,hSB,Bphase,hBphase,hphaseProfiles⟩ :=
    exists_history_selected_complete_phase_profiles c hε hεtarget hAp.le hsrcε
      Gref hr hrR hR ext hextcenter hextradius hBband hStar horder
  obtain ⟨SA,hSA,Bamp,hBamp,hampProfiles⟩ :=
    exists_history_selected_amplitude_profiles f p Gref hr hrR hR ext hextcenter hextradius
      hBband h12 horder hε (by linarith : ε ≤ c.bufferRadius/2) hsrcε threshold Damp hDamp hcoverage
  have hstrict : 4*ε < c.targetRadius := by linarith [c.bufferRadius_pos]
  obtain ⟨δ,hδ,hδhalf,hδg,χg,hχg,hcχg,hsχg,heg,hrep⟩ :=
    SmoothRepresentative.exists_common_smooth_representative c.radialSection
      (isCompact_closedBall (z.1,z) (4*ε)) isOpen_ball (closedBall_subset_ball hstrict)
      (by norm_num : (0 : ℝ) < 1/2) (div_pos hg (by positivity : 0 < 1+‖c.radialSection‖))
  let S₀ := max SP (max SB SA)
  refine ⟨S₀,hSP.trans (le_max_left _ _),?_⟩
  intro R₀ stage hist ell hR₀ hhist Q hQ B L h Φ chart G hbuffer hsm hdiff hnear hphase hsourceTime
    Fs matrix Ws hFs hmatrix hsupport hGsolver hGres hbudget hsourceBand hradial
    Op hOp e Mo Mi capped negative P₀ hP₀ gap hgap rawSource hangle
    lam K A₀ hlam hLK hscale hA₀ S hS hSU a ha has Csource hfourier hparam φ hprimary
  have hSPi i : SP ≤ R₀ i := (le_max_left _ _).trans (hR₀ i)
  have hSBi i : SB ≤ R₀ i := (le_max_left _ _).trans ((le_max_right _ _).trans (hR₀ i))
  have hSAi i : SA ≤ R₀ i := (le_max_right _ _).trans ((le_max_right _ _).trans (hR₀ i))
  have hL i : 1 ≤ L i := one_le_currentCoefficientScale (by linarith [hSPi i]) (stage i)
  have hp i := (hprimaryProfiles (Q i)).2.2 (R₀ i) (hSPi i) (stage i) (hist i) (ell i)
    (hhist i) (hQ i)
  have hφ i : ContDiff ℝ ∞ (Function.uncurry (φ i)) :=
    (hprimary i).comp (contDiff_snd.prodMk contDiff_fst)
  intro o
  dsimp only
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
  obtain ⟨_,hχsMask,hcχsource₀,hcχsource,_⟩ := chartPhysicalMasks_properties f p
  let χo := endpointOutputMask f p output
  let χs := chartInputMask f p
  let X₀ := tsupport χo ∪ tsupport χs
  have hX₀ : IsCompact X₀ := hcχout.union hcχsource
  let : CompactSpace X₀ := isCompact_iff_compactSpace.mp hX₀
  have hXU : X₀ ⊆ U := selected_common_physical_masks_subset_stationary_box f p z ε hmaskBox output hos
  have hSX : S ∪ X₀ ⊆ U := union_subset hSU hXU
  have hW i k : ContDiff ℝ ∞ (jointAmplitude (Ws i k)) :=
    (hmatrix i k).comp (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd)))
  let W := fun i ↦ if o=0 then Ws i 0+Ws i 1 else Ws i 2
  have hWo i : ContDiff ℝ ∞ (jointAmplitude (W i)) := by
    by_cases hz : o=0
    · simp only [W,ite_eq_left hz]
      change ContDiff ℝ ∞ (jointAmplitude (Ws i 0) + jointAmplitude (Ws i 1))
      exact (hW i 0).add (hW i 1)
    · simpa only [W,ite_eq_right hz] using hW i 2
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
  have hactions i := selected_once_capped_operator_actions f p hbufferTarget hsrcBuffer
    output ho hoc hos hob threshold hthreshold angular hang hangPlateau
    (Q i).1 (B i) (h i) (Φ i) (chart i) (hbuffer i) (hsm i) (hdiff i) (hnear i) (hphase i)
    (hsourceTime i) (hFs i) (hmatrix i) (hsupport i) (G i) (hGsolver i) (hGres i)
    χout χsource hχsource base cost (Op i) (hOp i) hlocalout hlocalin
  have hphaseEq i t (ht : t ∈ Icc 0 (3*c.maskRadius/4)) x y ξ
      (hA : elapsedAmplitude (W i) χo χs β t x y ξ ≠ 0) :
      elapsedPhase (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) t x ξ = elapsedPhase (Ψ i) t x ξ := by
    by_cases hz : o=0
    · apply capped_solver_phase_eq_representative_on_amplitude c.radialSection z hε hsrcε
        (chart i) hδ hδhalf heg (matrix i 0) (matrix i 1) (G i) (hGsolver i)
        χo χs β (subset_union_left.trans hXU) hβD ht x y ξ
      simpa only [W,ite_eq_left hz,matrix,Ws,selectedConicAmplitude] using hA
    · apply capped_residual_phase_eq_representative_on_amplitude c.radialSection z hε hsrcε
        (chart i) hδ hδhalf heg (matrix i 2) (G i) c.timeMask (hGres i)
        χo χs β (subset_union_left.trans hXU) htimePlateau hβD ht x y ξ
      simpa only [W,ite_eq_right hz,matrix,Ws,selectedConicAmplitude] using hA
  have hIntegral i v : capped i o v = elapsedGraphIntegral (3*c.maskRadius/4)
      (Ψ i) (W i) χo χs β v := by
    rw [(hactions i).2.1 o v]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change elapsedGraph (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (W i) χo χs β t v =
      elapsedGraph (Ψ i) (W i) χo χs β t v
    rw [show elapsedGraph (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (W i) χo χs β t =
      elapsedGraph (Ψ i) (W i) χo χs β t from
      fullGraphOperator_phase_congr _ _ _ (hphaseEq i t ht)]
  have hIntegralAdj i v : (capped i o).adjoint v = ∫ t in Icc 0 (3*c.maskRadius/4),
      (elapsedGraph (Ψ i) (W i) χo χs β t).adjoint v := by
    rw [(hactions i).2.2 o v]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change (elapsedGraph (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (W i) χo χs β t).adjoint v =
      (elapsedGraph (Ψ i) (W i) χo χs β t).adjoint v
    rw [show elapsedGraph (fun t s y ξ ↦ G i (t,(s,(y,ξ)))) (W i) χo χs β t =
      elapsedGraph (Ψ i) (W i) χo χs β t from
      fullGraphOperator_phase_congr _ _ _ (hphaseEq i t ht)]
  have hKP {y : E} {b : Par} (hy : y ∈ U) (hb : b ∈ V) : (y,b) ∈ KP :=
    ⟨subset_closure (UniformEvolution.closure_elapsedPhysicalBox_half_subset hε (subset_closure hy)),
      subset_closure hb⟩
  have hφgerm i b (hb : b ∈ V) y (hy : y ∈ U) : φ i b =ᶠ[𝓝 y] rawSource i b := by
    filter_upwards [(heχp (y,b) (hKP hy hb)).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt] with z hz
    change χp (z,b) = 1 at hz
    cases negative <;> simp only [φ,rawSource,Bool.false_eq_true,↓reduceIte,hz,one_mul]
  let φ₀ := fun i b y ↦ if negative then
    -(χp₀ (y,b)*T.fullSourcePhaseInCoordinates c.index (Q i) y b)
    else χp₀ (y,b)*T.fullSourcePhaseInCoordinates c.index (Q i) y b
  have hφcompare i b (hb : b ∈ V) y (hy : y ∈ U) :
      Function.uncurry (φ i) =ᶠ[𝓝 (b,y)] Function.uncurry (φ₀ i) := by
    filter_upwards [(heχp (y,b) (hKP hy hb)).comp_tendsto
      (continuous_snd.prodMk continuous_fst).continuousAt,
      (heχp₀ (y,b) (hKP hy hb)).comp_tendsto
        (continuous_snd.prodMk continuous_fst).continuousAt] with q hq hq₀
    change χp (q.2,q.1) = 1 at hq
    change χp₀ (q.2,q.1) = 1 at hq₀
    cases negative <;> simp only [Function.uncurry,φ,φ₀,Bool.false_eq_true,↓reduceIte,hq,hq₀,c]
  have hφbounds i j b (hb : b ∈ V) y (hy : y ∈ U) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) (b,y)‖ ≤ Bprimary j*L i^(j-Rstar) ∧
      ‖iteratedFDeriv ℝ j (φ i b) y‖ ≤ Bprimary j*L i^(j-Rstar) := by
    have hjoint := hφcompare i b hb y hy
    have hspatial : φ i b =ᶠ[𝓝 y] φ₀ i b := hjoint.comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
    rw [(hjoint.iteratedFDeriv ℝ j).eq_of_nhds,
      (hspatial.iteratedFDeriv ℝ j).eq_of_nhds]
    have hh := (hp i).1 j (y,b) (hKP hy hb)
    cases negative
    · exact hh
    · change ‖iteratedFDeriv ℝ j
        (-(fun q : Par × E ↦ χp₀ (q.2,q.1)*T.fullSourcePhaseInCoordinates c.index (Q i) q.2 q.1))
        (b,y)‖ ≤ _ ∧
        ‖iteratedFDeriv ℝ j
          (-(fun y ↦ χp₀ (y,b)*T.fullSourcePhaseInCoordinates c.index (Q i) y b)) y‖ ≤ _
      rw [iteratedFDeriv_neg_apply,iteratedFDeriv_neg_apply,norm_neg,norm_neg]
      exact hh
  have hsourceNorm i b (hb : b ∈ V) y (hy : y ∈ U) :
      a₀ ≤ ‖fderiv ℝ (φ i b) y‖ ∧ ‖fderiv ℝ (φ i b) y‖ ≤ B₀ := by
    rw [(hφgerm i b hb y hy).fderiv_eq]
    have hh := hsourceBand i (y,b) (hKP hy hb)
    cases negative
    · exact hh
    · simpa only [rawSource,↓reduceIte,fderiv_fun_neg,norm_neg] using hh
  let χoj := fun j ↦ cNorm (S ∪ X₀) j χo
  let χsj := fun j ↦ cNorm (S ∪ X₀) j χs
  have hχoj j : 0 ≤ χoj j := cNorm_nonneg ..
  have hχsj j : 0 ≤ χsj j := cNorm_nonneg ..
  have hojet j y (hy : y ∈ S ∪ X₀) : ‖iteratedFDeriv ℝ j χo y‖ ≤ χoj j :=
    norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (hχout.of_le (by simp)) hy le_rfl
  have hsjet j y (hy : y ∈ S ∪ X₀) : ‖iteratedFDeriv ℝ j χs y‖ ≤ χsj j :=
    norm_iteratedFDeriv_le_cNorm (hS.union hX₀) (hχsMask.of_le (by simp)) hy le_rfl
  have hβs : ContDiff ℝ ∞ β := (selectedEndpointMultiplier_bounds f p threshold).1
  have hβb : ∀ ξ, ‖β ξ‖ ≤ 1 := (selectedEndpointMultiplier_bounds f p threshold).2
  let ac := fun i b y ↦ a i (y,b)
  have hac i : ContDiffOn ℝ ∞ (Function.uncurry (ac i)) (V ×ˢ univ) :=
    ((ha i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have hasc i b (_hb : b ∈ V) : tsupport (ac i b) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra hys
    exact hy (has i (y,b) hys)
  have hPφ i b (hb : b ∈ V) y (hy : y ∈ S) k (_hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k+1) (φ i b) y‖ ≤ Bprimary (k+1)*L i^k :=
    ((hφbounds i (k+1) b hb y (hSU hy)).2).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (by omega)) (hBprimary _))
  have hΔ : 0 ≤ 3*c.maskRadius/4 := by
    have hh := c.maskRadius_pos
    positivity
  have hΨgerm i t (ht : t ∈ Icc 0 (3*c.maskRadius/4)) ξ (hξ : β ξ ≠ 0) y (hy : y ∈ U) :
      (fun v ↦ elapsedPhase (Ψ i) t v ξ) =ᶠ[𝓝 y]
        (fun v ↦ elapsedPhase (curriedPhase c.radialSection (chart i)) t v ξ) := by
    have hξD := hβD (subset_tsupport _ hξ)
    exact (SmoothRepresentative.elapsed_representative_eventuallyEq c.radialSection (chart i)
      hδ heg (capped_elapsedPoint_mem_phase_plateau c.radialSection z hε hsrcε ht hy hξD)
      (hδhalf.trans hξD.2.le)).comp_tendsto
        (continuous_id.prodMk continuous_const).continuousAt
  have hradialRep i t (ht : t ∈ Icc 0 (3*c.maskRadius/4)) ξ (hξ : β ξ ≠ 0) y (hy : y ∈ U) :
      m*‖ξ‖ ≤ ‖fderiv ℝ (fun v ↦ elapsedPhase (Ψ i) t v ξ) y‖ ∧
      ‖fderiv ℝ (fun v ↦ elapsedPhase (Ψ i) t v ξ) y‖ ≤ Mfreq*‖ξ‖ := by
    rw [(hΨgerm i t ht ξ hξ y hy).fderiv_eq]
    exact hradial i t ⟨ht.1,by linarith [ht.2,c.maskRadius_pos]⟩ y hy ξ
      (hβD (subset_tsupport _ hξ))
  have hPΘ i t (ht : t ∈ Icc 0 (3*c.maskRadius/4)) ξ (hξ : β ξ ≠ 0)
      y (hy : y ∈ S) k (hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k+1) (fun v ↦ elapsedPhase (Ψ i) t v ξ) y‖ ≤
        (3*Bphase (k+1))*‖ξ‖*L i^k := by
    have hd := norm_iteratedFDeriv_elapsedPhase_source_le isOpen_univ
      (Ψ i) (hΨ i).contDiffOn t ξ y (mem_univ _) k hk
    have hb := hphaseProfiles (R₀ i) (hSBi i) (stage i) (hist i) (ell i) (hhist i)
      (chart i) (hbuffer i) (hsm i) (by simpa only [← hQ i] using hphase i)
      δ hδ hδhalf χg heg t ht ξ (hβD (subset_tsupport _ hξ)) (k+1) y (hSU hy)
    simp only [Nat.add_sub_cancel] at hb
    have hn := retainedFrequencyDomain_norm_lt c.radialSection (hβD (subset_tsupport _ hξ))
    apply (hd.trans hb).trans
    have hfac : 1+‖ξ‖ ≤ 3*‖ξ‖ := by linarith
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfac (hBphase (k+1)))
      (pow_nonneg (zero_le_one.trans (hL i)) k)).trans_eq (by ring)
  let sourceGap := min gap 1*min a₀ 1/4
  have hsourceGap : 0 < sourceGap := by dsimp only [sourceGap]; positivity
  cases adj
  · have hfreq i ξ (hξ : β ξ ≠ 0) b (hb : b ∈ V) (hbP : b ∈ P₀) y (hy : y ∈ U) :
        sourceGap*(lam i+‖ξ‖) ≤
          ‖lam i • fderiv ℝ (φ i b) y-InnerProductSpace.toDual ℝ E ξ‖ := by
      apply inactive_source_dual_frequency_gap (φ i b) y ξ ha₀ hgap (zero_lt_one.trans_le (hlam i))
      · simpa only [gradient,LinearIsometryEquiv.norm_map] using (hsourceNorm i b hb y hy).1
      · intro _
        change gap ≤ dist (NormedSpace.normalize ((InnerProductSpace.toDual ℝ E).symm
          (fderiv ℝ (φ i b) y))) (NormedSpace.normalize ξ)
        rw [(hφgerm i b hb y hy).fderiv_eq]
        exact hangle i b hb hbP 0 ⟨le_rfl,hΔ⟩ y hy ξ (subset_tsupport _ hξ)
    apply inactive_fullSource_elapsed_operator_sobolev hV hP₀ hX₀ hS
      (isOpen_elapsedPhysicalBox _ _) hSU hXU hΔ
      hν hν1 hsourceGap (fun k ↦ Bprimary (k+1)) Bphase Bprimary χoj χsj Bamp Csource 1
      (fun k ↦ hBprimary _) hBphase hBprimary hχoj hχsj hBamp zero_le_one
      lam L K A₀ hlam hL hLK hscale hA₀ Ψ W (fun _ ↦ χo) (fun _ ↦ χs) (fun _ ↦ β)
      φ ac hac hasc hparam (fun _ ↦ Subset.rfl) (fun _ ↦ hχout) (fun _ ↦ hχsMask)
      (fun _ ↦ hβs) (fun _ ↦ hβb) hΨ hWo hφ
      ?_ ?_ ?_ (fun _ ↦ hojet) (fun _ ↦ hsjet) hfourier
      (fun i b hb y hy ↦ (hsourceNorm i b hb y hy).2) hfreq hPφ
      (fun i ↦ Creg i o) (fun i ↦ hgraphs i o) (fun i ↦ capped i o) hIntegral
      (fun i b ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b))
      (fun i b _ ↦ vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] b)
    · intro i t ht ξ hξ j y hy
      have hh := hphaseProfiles (R₀ i) (hSBi i) (stage i) (hist i) (ell i) (hhist i)
        (chart i) (hbuffer i) (hsm i) (by simpa only [← hQ i] using hphase i)
        δ hδ hδhalf χg heg t ht ξ (hβD (subset_tsupport _ hξ)) j y (hSX hy)
      exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le _ _))
        (mul_nonneg (hBphase _) (by positivity)))
    · intro i j b hb y hy
      exact ((hφbounds i j b hb y (hSX hy)).1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le _ _)) (hBprimary _))
    · intro i t ht ξ hξ j y hy
      simpa only [← hQ i,fullElapsedPhysicalFactor,matrix,Fs,Ws,selectedConicAmplitude,B,L,c,W] using
        hampProfiles (R₀ i) (hSAi i) (stage i) (hist i) (ell i) (hhist i)
          (Φ i) (chart i) angular (by simpa only [← hQ i] using hmatrix i)
          (by simpa only [← hQ i] using hbudget i) t ht ξ (subset_tsupport _ hξ) j y (hSX hy) o
  · have hfreq i t (ht : t ∈ Icc 0 (3*c.maskRadius/4)) ξ (hξ : β ξ ≠ 0)
        b (hb : b ∈ V) (hbP : b ∈ P₀) y (hy : y ∈ U) :
        (sourceGap*m)*(lam i+‖ξ‖) ≤
          ‖lam i • fderiv ℝ (φ i b) y-fderiv ℝ (fun v ↦ elapsedPhase (Ψ i) t v ξ) y‖ := by
      apply (inactive_adjoint_source_dual_frequency_gap (elapsedPhase (Ψ i) t) (φ i b)
        y ξ ha₀ hgap hm hm1 (zero_lt_one.trans_le (hlam i))
        (by simpa only [gradient,LinearIsometryEquiv.norm_map] using (hsourceNorm i b hb y hy).1)
        (hradialRep i t ht ξ hξ y hy).1 ?_).2
      intro _
      simp only [gradient,(hφgerm i b hb y hy).fderiv_eq,(hΨgerm i t ht ξ hξ y hy).fderiv_eq]
      exact hangle i b hb hbP t ht y hy ξ (subset_tsupport _ hξ)
    apply inactive_fullSource_adjoint_elapsed_operator_sobolev hV hP₀ hX₀ hS
      (isOpen_elapsedPhysicalBox _ _) hSU hXU hΔ
      hν hν1 (mul_pos hsourceGap hm) hMfreq (fun k ↦ Bprimary (k+1))
      (fun k ↦ 3*Bphase (k+1)) Bphase Bprimary χoj χsj Bamp Csource 1
      (fun k ↦ hBprimary _) (fun k ↦ mul_nonneg (by norm_num) (hBphase _))
      hBphase hBprimary hχoj hχsj hBamp zero_le_one
      lam L K A₀ hlam hL hLK hscale hA₀ Ψ W (fun _ ↦ χo) (fun _ ↦ χs) (fun _ ↦ β)
      φ ac hac hasc hparam (fun _ ↦ Subset.rfl) (fun _ ↦ hχout) (fun _ ↦ hχsMask)
      (fun _ ↦ hβs) (fun _ ↦ hβb) hΨ hWo hφ
      ?_ ?_ ?_ (fun _ ↦ hojet) (fun _ ↦ hsjet) hfourier
      (fun i b hb y hy ↦ (hsourceNorm i b hb y hy).2)
      (fun i t ht ξ hξ y hy ↦ (hradialRep i t ht ξ hξ y hy).2) hfreq hPφ hPΘ
      (fun i ↦ Creg i o) (fun i ↦ hgraphs i o) (fun i ↦ (capped i o).adjoint) hIntegralAdj
      (fun i b ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] b))
      (fun i b _ ↦ vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] b)
    · intro i t ht ξ hξ j y hy
      have hh := hphaseProfiles (R₀ i) (hSBi i) (stage i) (hist i) (ell i) (hhist i)
        (chart i) (hbuffer i) (hsm i) (by simpa only [← hQ i] using hphase i)
        δ hδ hδhalf χg heg t ht ξ (hβD (subset_tsupport _ hξ)) j y (hSX hy)
      exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le _ _))
        (mul_nonneg (hBphase _) (by positivity)))
    · intro i j b hb y hy
      exact ((hφbounds i j b hb y (hSX hy)).1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le _ _)) (hBprimary _))
    · intro i t ht ξ hξ j y hy
      simpa only [← hQ i,fullElapsedPhysicalFactor,matrix,Fs,Ws,selectedConicAmplitude,B,L,c,W] using
        hampProfiles (R₀ i) (hSAi i) (stage i) (hist i) (ell i) (hhist i)
          (Φ i) (chart i) angular (by simpa only [← hQ i] using hmatrix i)
          (by simpa only [← hQ i] using hbudget i) t ht ξ (subset_tsupport _ hξ) j y (hSX hy) o

end JanetCartan.PhysicalPrimary
