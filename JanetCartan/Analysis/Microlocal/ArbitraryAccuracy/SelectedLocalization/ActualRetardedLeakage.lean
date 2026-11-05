module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhaseInputs
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualCollar
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SupportedPhaseApplication
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.UniformElapsedAmplitudeInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformSupported.Integrated
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors

/-!
# Actual retarded leakage on the retained residual carrier

The phase, amplitude and collar producers supply the primitive integrated
estimate on the same retained coefficients and even proof masks. Both literal
orientations use the original graph regularizations and elapsed intervals.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 256
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open Characteristic Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open EvolutionLocalization EvolutionIntegratedLocalization FourierIntegral FiniteChain.Graph
open FiniteChain.Graph.PhysicalShells
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Z" => RootState (Euclidean d)

open SelectedEvenProofMasks ProtectedMasks JanetCartan.Localization
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates
open JanetCartan.CharacteristicTransport.CompleteResidual
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open FiniteChain.Graph.PhysicalShells.Noncomparable
local notation "Mat" => MetricTensor (d+1)
local notation "V" => ℝ × JointVariables E

open FiniteChain.Graph.KernelLimits FourierIntegral.LowBounds FourierIntegral.LowBounds.FrequencyCutoff Pseudodifferential
open Characteristic.AmplitudeBounds Characteristic.UniformAmplitudes Characteristic.RootFamily
open Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.PdoRealization
local notation "Hspace" => SpacetimeL2 d (d+1)

/-- Apply the actual elapsed phase, amplitude and supported-collar producers
on one retained chart family, then the primitive integrated leakage theorem.
The only analytic certificates remaining are those of the original constructor
and its literal common graph regularizations. Constants precede the varying
coefficient field, even masks and accuracy, and the original elapsed interval,
full zeroth-order field and doubled radial shoulder are retained. Consumer:
the retarded letters of the complete normalized mixed residual words
(`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_retarded_fourier_leakage_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hρb : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ) (hra : ∀ p, 0 < ra p) (hab : ∀ p, ra p ≤ rb p)
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ a₀ b₀ : ℝ, 0 < a₀ →
      ∃ tlo thi : ℝ, 0 < tlo ∧ 0 < thi ∧
      ∀ output : E → ℝ, ContDiff ℝ ∞ output → HasCompactSupport output →
      tsupport output ⊆ ball x f.physicalRadius →
      ∀ threshold : ℝ, f.radialThreshold ≤ threshold →
      ∀ θ : f.centers → ℝ → ℂ, (∀ p, ContDiff ℝ ∞ (θ p)) →
      (∀ p, HasCompactSupport (θ p)) →
      (∀ p r, r ∈ Icc 0 (3*(f.chart p).maskRadius/4) → θ p r = 1) →
      (∀ p, tsupport (θ p) ⊆ ball 0
        (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius)) →
      ∀ {ι κ ιu ιz : Type*} [Fintype ι] [Fintype κ] [Fintype ιu] [Fintype ιz],
      ∀ (eT : Module.Basis ι ℝ (JointVariables E))
        (eI : Module.Basis κ ℝ (ℝ × JointVariables E))
        (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E),
      ∀ J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E,
      MeasurePreserving (graphInputCoordinates J) volume volume →
      ∀ (χ₂ : E → ℝ) (Ksource : Set E) (Vsource : Set (E × E)) (Γ : Set E)
        (N : ℕ) (n : f.centers → ℕ) (cRad : (p : f.centers) → Fin (n p) → ℝ)
        (hcRad : ∀ p k, 0 < cRad p k) (Urad : (p : f.centers) → Fin (n p) → Set Z)
        (buffer Rbase εcollar δT δI : ℝ) (Hmask Hcollar : ℕ → ℝ),
      (∀ j, 0 ≤ Hmask j) → (∀ j, 0 ≤ Hcollar j) →
      0 < εcollar → 0 < δT → 0 < δI →
      ∀ χ : V → ℂ, ContDiff ℝ ∞ χ →
      (∀ v, |v.1| ≤ εcollar / 4 → χ v = 1) →
      tsupport χ ⊆ {v | |v.1| ≤ εcollar / 2} →
      (∀ j v, ‖iteratedFDeriv ℝ j χ v‖ ≤ Hcollar j) →
      ∀ ψ : f.centers → E → ℝ, (∀ p, ContDiff ℝ ∞ (ψ p)) →
      (∀ p, HasCompactSupport (ψ p)) → (∀ p y, ‖ψ p y‖ ≤ 1) →
      (∀ p (backward : Bool) y, y ∈ (if backward then tsupport (chartInputMask f p)
        else tsupport (endpointOutputMask f p output)) → ψ p y = 1) →
      (∀ p y, y ∈ closedBall 0 Rbase → ψ p y = 1) →
      ∀ order : ℕ,
      ∃ (bLoss : f.centers → ℕ) (Cmq : f.centers → ℕ → ℝ),
      (∀ p q, 0 ≤ Cmq p q) ∧
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j-Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let h := fun p ↦ fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root
      let z := fun p ↦ ((coordinateSplit (f.chart p).index x).1,
        ((coordinateSplit (f.chart p).index x).2,
          (coordinateSplit (f.chart p).index p.val.val).2))
      let Fs := fun p ↦ selectedBufferedAmplitude f p Q B (Φ p) (Cchart p)
      let W := fun p (j : Fin 3) ↦
        collared (f.chart p).radialSection (if j=0 then 0 else 1) (angular p) (Fs p j)
      (∀ p, ContDiffOn ℝ ∞ (twoTimePhase (Cchart p)) (Cchart p).target) →
      (∀ p, closedBall ((z p).1, z p) (f.chart p).targetRadius ⊆ (Cchart p).target) →
      (∀ p, ∀ v ∈ (Cchart p).target, HasFDerivAt (twoTimePhase (Cchart p))
        (twoTimePhaseDifferential (h p) (Φ p) (Cchart p) v) v) →
      (∀ p, ∀ v ∈ closedBall ((z p).1, z p) (f.chart p).targetRadius,
        ‖twoTimePhaseMixed (Cchart p) v - 1‖ ≤ 1/2) →
      (∀ p j, cNorm (closedBall ((z p).1, z p) (f.chart p).targetRadius) j
        (twoTimePhase (Cchart p)) ≤ (f.chart p).phaseCost j *
          (1+cNorm (closedBall x RQ) (j+1) Q)) →
      (∀ p, ∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η) →
      (∀ p j, ContDiff ℝ ∞ (W p j)) →
      (∀ p, tsupport (Fs p 2) ⊆ closedBall ((z p).1, z p) ((f.chart p).bufferRadius/2)) →
      (∀ p, tsupport (W p 2) ⊆ ConicPhase.domain (f.chart p).radialSection
        ((Cchart p).target ∩ (Cchart p).symm ⁻¹'
          (ball (z p).1 ((f.chart p).maskRadius/2) ×ˢ
            (ball (z p).1 ((f.chart p).maskRadius/2) ×ˢ
              ball (z p).2 ((f.chart p).maskRadius/2))))) →
      (∀ p (v : T), (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
        ∀ j : Fin (d+1), (fun k ↦ W p 2 v k j) =
          WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
            (fun y k ↦ W p 1
              (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
            ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) →
      (∀ p, ∀ v ∈ (Cchart p).target, ((Cchart p).symm v).2.1 = v.2.1) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1)
          (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
            (ra p) (rb p)) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1)
          (bufferedJetSet (f.chart p).radialSection (z p) ((f.chart p).bufferRadius/2)
            (ra p) (rb p)) m
          (selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ (hEven : SelectedSectorEvenNestedMaskConclusion f eT eI χ₂ Ksource Vsource Γ output
        N (fun p ↦ ra p / thi) (fun p ↦ ra p / tlo) n cRad hcRad Urad
        buffer a₀ b₀ Rbase εcollar δT δI Hmask Q Φ Cchart) (k : Fin N) (p : f.centers),
      let masks := hEven.choose_spec.choose
      let mi := canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.castSucc)
      let mo := canonicalProofLocalizer (coordinateSplit (f.chart p).index) (masks k.succ)
      let Δ := 3*(f.chart p).maskRadius/4
      let χout := endpointOutputMask f p output
      let χsource := chartInputMask f p
      let β := selectedEndpointMultiplier f p threshold
      let Ψoriginal := curriedExtend (f.chart p).radialSection (twoTimePhase (Cchart p))
      let Aoriginal := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
      let Boriginal := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
      let W₀original := selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 0
      let W₁original := selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p) 1
    ∀ (Treg : ℕ → ℝ → Hspace →L[ℂ] Hspace)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d+1),
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψoriginal r)
        (frequencyCutFullAmplitude (complexPhysicalCutoff j) (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d+1),
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψoriginal r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (complexPhysicalCutoff j ξ))
            (fun x z ξ ↦ (elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hm : ∀ j u, AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)))
    (hmAdj : ∀ j u, AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)))
    {LOW : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ LOW)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψoriginal (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true) χout χsource β r).adjoint u))),
    ∀ Mi Mo Qop : Hspace →L[ℂ] Hspace,
      (∀ u : Hspace, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u : Hspace, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Qop u = elapsedGraphIntegral Δ Ψoriginal
        (directRetardedAmplitudes Aoriginal Boriginal W₀original W₁original true)
        χout χsource β u) →
      ∀ accuracy (backward : Bool) u,
      MemVectorFourierSobolev (order : ℝ)
        ((1 - Mo) ((if backward then Qop.adjoint else Qop) (Mi u))) ∧
      vectorFourierSobolevNorm (order : ℝ)
        ((1 - Mo) ((if backward then Qop.adjoint else Qop) (Mi u))) ≤
        Cmq p accuracy * ρ ^ ((order : ℝ) + (3 * (d+1) : ℕ)) *
          L ^ bLoss p * (L / ρ) ^ accuracy * ‖u‖ := by
  classical
  obtain ⟨c, C, hc, hC, hphase⟩ := exists_selected_supported_elapsed_phase_inputs
    (q := d+1) f hρb hsrcρ ra rb hra hab A hA
  refine ⟨c, C, hc, hC, ?_⟩
  intro a₀ b₀ ha₀
  obtain ⟨tlo, thi, htlo, hthi, hphase⟩ := hphase a₀ b₀ ha₀
  refine ⟨tlo, thi, htlo, hthi, ?_⟩
  intro output ho hoc hout threshold ht θ hθ hθs hθone hθbuffer
    ι κ ιu ιz _ _ _ _ eT eI eu ez J hJ χ₂ Ksource Vsource Γ N n cRad hcRad Urad
    buffer Rbase εcollar δT δI Hmask Hcollar hHmask hHcollar hε hδT hδI
    χ hχ hχone hχsupport hχder ψ hψ hψs hψb hψmask hψY order
  let Kg := fun p ↦ selectedResidualComparableCarrier f p output threshold c C a₀ b₀
  let Kjet := fun p ↦ selectedRetainedResidualCarrier f p output threshold c C a₀ b₀
    (θ p) (ra p) (rb p) tlo thi
  obtain ⟨hKg, hKjet, hsub, hsupport, P₀, Pbase, hP₀, hPbase, Vphase, Ua, Kphysical,
    hVphase, hUa, hKphysical, hKV, hUabuffer, hUapos, hphysicalMap, hcarrier, hphase⟩ :=
    hphase output ho hoc hout threshold ht θ hθs hθbuffer
  obtain ⟨Kglobal, Kelapsed, Qt, Qs, Qg, Qb, Qi, O, Wave, Bbase, D,
    hKg', hKe, heq, hglobal, hcover, hQt, hQs, hQg, hQb, hQi, hO, hWave, hBbase,
    hD₁, hD₂, hD₃, hD₄, hD₅, hamp⟩ :=
    exists_selected_elapsed_amplitude_inputs_of_joint_localizer_profile f hρb hsrcρ
      c C a₀ b₀ ha₀ ra rb hra hab cost hcost A hA output ho hoc hout threshold ht
      (fun p ↦ 3*(f.chart p).maskRadius/4) θ hθs hθone Hmask hHmask
  have hKgEq : Kglobal = Kg := funext (fun p ↦ hglobal p)
  subst Kglobal
  obtain ⟨δT', δI', G, hδT', hδI', hphase⟩ := hphase eT eI χ₂ Ksource Vsource Γ
    N n cRad hcRad Urad buffer Rbase εcollar δT δI Hmask Hcollar
    hε hδT hδI χ hχ hχone hχsupport hχder ψ hψs
  choose Cβ hCβ hcone using
    (fun p ↦ exists_selectedEndpointMultiplier_temporal_cone f p (hρb p) (hsrcρ p))
  have htpos : 0 < threshold := zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)
  have hΔ (p : f.centers) : 0 ≤ 3*(f.chart p).maskRadius/4 := by
    have hmr := (f.chart p).maskRadius_pos
    positivity
  have hbound (p : f.centers) :=
    ResidualLocalization.UniformSupported.exists_supported_directResidual_integral_fourier_bound_of_uniform_masks
      (q := d+1) eT eI eu ez J hJ (-1) (3*(f.chart p).maskRadius/4) (hΔ p)
      order 0 0 0 0 0 0 0 c C b₀ hc ha₀ (by norm_num : (0 : ℝ) ≤ 1)
      (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointMultiplier f p threshold)
      (endpointOutputMask_properties f p ho hoc hout).1
      (chartPhysicalMasks_properties f p).2.1
      (selectedEndpointMultiplier_bounds f p threshold).1
      (endpointOutputMask_properties f p ho hoc hout).2.1
      (chartPhysicalMasks_properties f p).2.2.2.1 (by norm_num : (0 : ℝ) ≤ 1)
      (hCβ p) (selectedEndpointMultiplier_bounds f p threshold).2
      (hcone p threshold htpos) Pbase Bbase O hPbase hBbase hO (hKjet p)
      (δT' p) (δI' p) (G p) (G p) (hδT' p) (hδI' p)
      P₀ Hcollar Wave O Qt Qs Qg Qb Qi hP₀ hQt hQs hQg hQb hQi hHcollar hWave hO
      (closedBall 0 Rbase) (isCompact_closedBall 0 Rbase) (ψ p) (hψ p) (hψs p) (hψb p)
      (θ p) (hθ p) (hθs p) (hθone p) D (hKg p)
  choose bLoss Cmq Cpair Creal hCmq hCpair hCreal hbound using hbound
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular h z Fs W
    hphaseSmooth hphaseBuffer hdiff hnear hphaseCost hang hW hFs hWs hphysical hsourceTime hseminorm
    hEven k p masks mi mo Δ χout χsource β Ψoriginal Aoriginal Boriginal W₀original W₁original
    Treg hreal hrealAdj hm hmAdj LOW hLOW hlim hlimAdj Mi Mo Qop hMi hMo hQop accuracy backward u
  obtain ⟨Ψ, g, hΨ, hΨon, hbase, hgerm, hnormalizedGerm, hnormalizedJets,
    hagree, hphysicalPhase, hg, hcomp, hcollars⟩ :=
    hphase Rstar hRstar L hL Q hQ h Φ Cchart hphaseSmooth hphaseBuffer hdiff hnear hphaseCost
  obtain ⟨_, _, _, _, _, _, _, _, _, hcan, hcanSupport, hcanJets, _⟩ :=
    hEven.choose_spec.choose_spec
  let mif := fun p : f.centers ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index)
    (masks k.castSucc)
  let mof := fun p : f.centers ↦ canonicalProofLocalizer (coordinateSplit (f.chart p).index)
    (masks k.succ)
  have hann (p : f.centers) : tsupport (mif p) ⊆ univ ×ˢ frequencyAnnulus a₀ b₀ :=
    fun _ hv ↦ ⟨mem_univ _, (hcanSupport k.castSucc p hv).2⟩
  have hamp' := hamp mif mof (fun p ↦ (hcan k.castSucc p).smooth)
    (fun p ↦ (hcan k.succ p).smooth) (hcanJets k.castSucc) (hcanJets k.succ) hann
    Rstar hRstar L ρ hL hρ Q B hQ hB Φ Cchart angular hang hW hFs hphysical hseminorm p
  obtain ⟨hbSmooth, hbNormalized, hbGlobal, hbPhysical, hprim, hwave, hoSlice, hcompAmp, hglobalSupport⟩ := hamp'
  obtain ⟨UT, UI, hε', hχ', hχone', hdomains⟩ := hcollars hEven k ρ hρ
  have hjet (u' y' : E) : elapsedOutputJetCarrier (Kjet p) mi mo u' y' ⊆
      elapsedOutputJetCarrier (Kelapsed p) mi mo u' y' := by
    intro v hv
    refine ⟨?_, hv.2⟩
    rw [heq p]
    exact hsub p hv.1
  have hsupp := hsupport p Q B (Φ p) (Cchart p) (angular p)
    (hang p) (hW p) (hphysical p) (hsourceTime p) (hFs p) (hWs p)
  have haux := selected_common_smooth_direct_residual f p (hρb p) (hsrcρ p)
    output hout Q B (W p) (hW p) (hphysical p)
  have hslab := selected_common_residual_retarded_buffer f p (hρb p) (hsrcρ p)
    output hout (Cchart p) (hsourceTime p) (W p 2) (hWs p)
  let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
  let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
  let b := directRetardedAmplitudes Ac Bc W₀original W₁original true
  have hb : ∀ t s y η, s ≤ (z p).1 - (f.chart p).maskRadius/2 → b t s y η = 0 := by
    rw [show b = _ from haux.1]
    exact hslab.1
  obtain ⟨hiAnn, hiBound⟩ := selected_completeFactor_sliced_localizer_inputs
    (fun v hv ↦ (hcanSupport k.castSucc p hv).2) (hcan k.castSucc p).range
  have hbasei : Prod.fst '' tsupport mi ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hcanSupport k.castSucc p hv).1
  have hbaseo : Prod.fst '' tsupport mo ⊆ closedBall 0 Rbase := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hcanSupport k.succ p hv).1
  have hresult := hbound p mi mo (hcan k.castSucc p).smooth (hcan k.succ p).smooth
    (hcan k.succ p).range (hcan k.castSucc p).compactSupport (hcan k.succ p).compactSupport
    hiAnn hiBound Ψoriginal ρ L hρ hL Ac Bc W₀original W₁original true (Ψ p) (hΨ p)
    Aoriginal Boriginal W₀original W₁original hbSmooth
    (fun r _ ↦ hsupp.1 r) (Ua p) (Ua p) (hUa p) (hΨon p) (hbase p)
    (fun v hv j ↦ by simpa only [Nat.add_zero] using hbPhysical v (hUabuffer p hv) (hUapos p v hv) j)
    (fun r hr _ _ ξ _ v hv hβ ↦ hphysicalMap p r hr (ρ • ξ) (subset_tsupport _ hβ) v hv)
    (by simpa only [Nat.add_zero] using hoSlice)
    (hψmask p) (fun y hy ↦ hψY p y (hbaseo hy)) hbasei
    (hagree p b)
    (fun bw y _ low j l hc ↦ (hsupp.2 mi mo univ (hann p) bw ρ hρ low j l hc y).1)
    ((z p).1 - (f.chart p).maskRadius/2)
    ((z p).1 - (f.chart p).maskRadius/2 + 3*(f.chart p).maskRadius/4)
    hb hslab.2.1 hslab.2.2.le
    (fun _ _ _ ↦ χ) (UT p) (UI p) (εcollar/4) hε'
    (fun _ _ _ _ _ ↦ hχ')
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).1)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.1)
    (fun _ _ _ _ _ ↦ hχone')
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.1)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.2.1)
    (fun bw u' hu y' hy r hr v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.1 r hr v hv).1)
    (fun bw u' hu y' hy r hr v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.1 r hr v hv).2)
    (fun bw u' hu y' hy v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.2.1 v hv).1)
    (fun bw u' hu y' hy v hv ↦ ((hdomains p bw u' hu y' hy).2.2.2.2.2.1 v hv).2)
    (fun u' hu y' hy ↦ (hdomains p false u' hu y' hy).2.2.2.2.2.2.2)
    (fun bw u' hu y' hy ↦ (hdomains p bw u' hu y' hy).2.2.2.2.2.2.1)
    (fun u' _ y' _ v hv j ↦ (hwave u' y' v (hjet u' y' hv) j).1)
    (fun u' _ y' _ v hv j ↦ by simpa only [Nat.add_zero] using (hwave u' y' v (hjet u' y' hv) j).2)
    (fun u' _ y' _ v hv j ↦ by simpa only [Nat.add_zero] using hprim u' y' v (hjet u' y' hv) j)
    (fun _ ↦ Vphase p) (fun _ ↦ Kphysical p) (g p)
    (fun _ _ ↦ hVphase p) (fun _ _ ↦ hKphysical p) (fun _ _ ↦ hKV p)
    (hphysicalPhase p) (hcarrier p b ρ (zero_lt_one.trans_le hρ).ne')
    (hg p) (hcomp p) hcompAmp
    (fun bw low j l hc r _ y ↦ (hglobalSupport bw low j l hc y).1 r)
    (tsupport β) (isClosed_tsupport β)
    (zero_notMem_selectedEndpointMultiplier_tsupport f p
      (zero_lt_one.trans_le (f.radialThreshold_ge_one.trans ht)))
    (subset_refl _) complexPhysicalCutoff (fun _ _ _ ↦ rfl) Treg hreal hrealAdj hm hmAdj
    hLOW hlim hlimAdj Mi Mo Qop hMi hMo hQop
  simpa only [max_eq_left (by norm_num : (-1 : ℝ) ≤ 0), zero_add] using
    hresult.2.2.2.1 accuracy backward u

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
