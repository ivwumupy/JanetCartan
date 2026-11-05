module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SupportedPdoProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal.Fourier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredPdoInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness

/-!
# Actual measured selected PDO leakage with uniform proof-mask constants

Apply the selected symbol profiles and all-four-branch literal regularizations
to the diagonal leakage estimate. The resulting estimate is on the original
source, endpoint and differentiated algebraic operators and their adjoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 256
set_option maxRecDepth 4096
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual ResidualLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicChart RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.Characteristic.ConicPhase
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open RegularSector.FinitePdo.RetainedConstruction
open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

local notation "Hspace" => SpacetimeL2 d (d+1)
open KernelLimits LowBounds LowBounds.FrequencyCutoff Pseudodifferential
open EvolutionIntegratedLocalization
open RegularSector.Characteristic.PdoRealization

/-- The actual selected symbol and normal-amplitude producers give leakage
for the original measured PDO compositions. Both physical measurement masks
remain inside their own positions in the full amplitude. Constants precede
varying proof masks, coefficients, histories and scales. This is the actual
PDO input to `finiteChain_observation_rapidDecayAt.hleak`, retaining full `B`,
the doubled threshold and both literal orientations
(`app:ch_regular_base:eq:measured-adjoint`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_measured_threePDO_fourier_leakage_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col A₀ p.val.val c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall A₀ f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hchartBuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) {a b : ℝ} (ha : 0 < a)
    (Hmask : ℕ → ℝ) (hHmask : ∀ j, 0 ≤ Hmask j)
    {ι ιu ιz : Type*} [Fintype ι] [Fintype ιu] [Fintype ιz]
    (e : Module.Basis ι ℝ (JointVariables E))
    (eu : OrthonormalBasis ιu ℝ E) (ez : OrthonormalBasis ιz ℝ E)
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (Y : f.centers → Set E) (hY : ∀ p, IsCompact (Y p))
    (ψ : f.centers → E → ℝ) (hψ : ∀ p, ContDiff ℝ ∞ (ψ p))
    (hψs : ∀ p, HasCompactSupport (ψ p))
    (hψplateau : ∀ p backward y, y ∈ leakageOutputCarrier backward
      (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)) (Y p) → ψ p y = 1)
    {buffer : ℝ} (hbuffer : 0 < buffer) (order : ℕ) :
    ∃ (bLoss : f.centers → Fin 3 → Bool → ℕ)
      (Cmq : f.centers → Fin 3 → Bool → ℕ → ℝ),
      (∀ p j backward N, 0 ≤ Cmq p j backward N) ∧
      ∀ (mi mo : f.centers → LocalizerSymbol (d+1))
        (Ko Oo : f.centers → Set (E × E)),
      (∀ p, ContDiff ℝ ∞ (mi p)) → (∀ p, HasCompactSupport (mi p)) →
      (∀ p z, mi p z ∈ Icc (0 : ℝ) 1) →
      (∀ p, IsBufferedLocalizer (mo p) (Ko p) (Oo p)) →
      (∀ p, ∀ z ∈ tsupport (mi p), closedBall z buffer ⊆ interior {z | mo p z = 1}) →
      (∀ p, ∀ z ∈ tsupport (mi p), z.2 ∈ frequencyAnnulus a b) →
      (∀ p, Prod.fst '' tsupport (mi p) ⊆ Y p) →
      (∀ p, Prod.fst '' tsupport (mo p) ⊆ Y p) →
      (∀ p k z, ‖iteratedFDeriv ℝ k (mi p) z‖ ≤ Hmask k) →
      (∀ p k z, ‖iteratedFDeriv ℝ k (mo p) z‖ ≤ Hmask k) →
      ∀ Rstar : ℕ, 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
        (∀ k, cNorm (closedBall x RQ) k B ≤ AQ k * L ^ (k-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (Cchart : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let Kj := fun p ↦
        let ec := coordinateSplit (f.chart p).index
        let z : Z := ((ec x).1, ((ec x).2, (ec p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (Cchart p) (angular p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p 1))) →
      (∀ p j k, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (Kj p) k (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (Kj p) k (W p j) ≤
          cost p k * (1+cNorm (closedBall x RQ) (k+10) Q+cNorm (closedBall x RQ) (k+9) B)) →
      (∀ y, ‖output y‖ ≤ 1) →
      ∀ (Ralg Malg : Fin 2 → f.centers → ℝ) (Rend Mend : f.centers → ℝ),
      (∀ o p, GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2*threshold) Q B o)) (Ralg o p) (Malg o p)) →
      (∀ p, GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p threshold Q (W p 1))) (Rend p) (Mend p)) →
      ∀ (p : f.centers) (branch : Fin 3) (backward : Bool),
      let P := RegularSector.FiniteAssembly.measuredOperator
        (μ ∘ physicalCoordinates (f.chart p).index) (ν ∘ physicalCoordinates (f.chart p).index)
        (hμ.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (hν.continuous.comp (physicalCoordinates (f.chart p).index).continuous)
        (fun y ↦ hμb _) (fun y ↦ hνb _)
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (![selectedSourceSymbol f p (2*threshold),
          selectedEndpointSymbol f p threshold Q (W p 1),
          selectedAlgebraicSymbol f p (2*threshold) Q B 1] branch))
      let Top := if backward then P.adjoint else P
      ∀ (Mi Mo : Hspace →L[ℂ] Hspace),
      (∀ u, Mi u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ (mi p) (fun z ↦ (u z).ofLp) y)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Mo u =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (leftLocalizer ρ (mo p) (fun z ↦ (u z).ofLp) y)) →
      ∀ N u,
      MemVectorFourierSobolev (order : ℝ) ((1 - Mo) (Top (Mi u))) ∧
      vectorFourierSobolevNorm (order : ℝ) ((1 - Mo) (Top (Mi u))) ≤
        Cmq p branch backward N * ρ ^ ((order : ℝ) + (3 * (d+1) : ℕ)) *
          L ^ bLoss p branch backward * (L / ρ) ^ N * ‖u‖ := by
  classical
  obtain ⟨Dpdo, hDzero, hprofiles⟩ :=
    exists_selected_threePDO_grades_of_joint_localizer_profile f hΩ hRQ hball hc hdom
      threshold ht hft output ho hoc hout hchartBuffer hmask ra rb hcoverage cost hcost AQ hAQ
      (b := b) ha Hmask hHmask
  choose Dm hsym hinProf houtProf hio hoo hoff hmeasure using
    fun j ↦ exists_measured_maskedPDO_symbol_profiles (q := d+1) μ ν hμ hν hμc hνc (Dpdo j)
  let ec := fun p : f.centers ↦ RegularSector.FiniteEvolution.physicalCoordinateIsometry (f.chart p).index
  let χo := fun p y ↦ (μ (ec p y) : ℂ) * endpointOutputMask f p output y
  let χs := fun p y ↦ (ν (ec p y) : ℂ) * chartInputMask f p y
  have hbase (p : f.centers) : tsupport (χo p) ×ˢ tsupport (χs p) ⊆
      tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p) :=
    Set.prod_mono tsupport_mul_subset_right tsupport_mul_subset_right
  have hplateau (p : f.centers) (backward : Bool) : ∀ y ∈ leakageOutputCarrier backward
      (tsupport (χo p) ×ˢ tsupport (χs p)) (Y p), ψ p y = 1 := by
    apply fun y hy ↦ hψplateau p backward y ?_
    cases backward <;> exact (Set.union_subset_union (Set.image_mono (hbase p)) Subset.rfl) hy
  have hbound (p : f.centers) (j : Fin 3) (backward : Bool) :=
    UniformDiagonal.exists_directPDO_fourier_bound_of_uniform_masks
      (q := d+1) (b := b) e eu ez backward 0 order ha (χo p) (χs p)
      (endpointOutputMask_properties f p ho hoc hout).2.1.mul_left
      (chartPhysicalMasks_properties f p).2.2.2.1.mul_left J hJ (ψ p) (hψ p) (hψs p)
      (Y p) (Y p) (hY p) (hY p) (hplateau p backward)
      (Dm j) Hmask hHmask hbuffer
  choose bLoss Cmq hCmq hbnd using hbound
  refine ⟨bLoss, Cmq, hCmq, ?_⟩
  intro mi mo Ko Oo hi his hirange hom hdiag hann hbasei hbaseo hmi hmo
    Rstar hRstar L ρ hL hLρ Q B hQ hB hQr hQp hBp Φ Cchart angular Kj W hW hWp
    hob Ralg Malg Rend Mend halg hend p branch backward P Top Mi Mo hMi hMo N u
  have hρ : 1 ≤ ρ := hL.trans hLρ
  obtain ⟨hinput, houtput, hsymbol⟩ := hprofiles mi mo hi (fun p ↦ (hom p).smooth) hmi hmo
  have hgrades := hsymbol Rstar hRstar L ρ hL hρ Q B hQ hB hQr hQp hBp Φ Cchart angular hW hWp p backward
  obtain ⟨hRawSmooth, _, _, _, _, _, _, _⟩ :=
    SelectedResidualInputs.exists_selected_fourPDO_regularizations f p threshold
      (zero_lt_one.trans_le ht) Q B (W p 1) output ho hoc hout hob
      (fun o ↦ halg o p) (hend p)
  obtain ⟨hP, hAsmooth, hF, hzero, hsupport, Preg, hAdj, hreal, hlim⟩ :=
    exists_selected_fourPDO_measured_regularizations f p threshold
      (zero_lt_one.trans_le ht) Q B (W p 1) output ho hoc hout hob
      (μ ∘ ec p) (ν ∘ ec p) (hμ.comp (ec p).contDiff) (hν.comp (ec p).contDiff)
      (fun y ↦ hμb _) (fun y ↦ hνb _) (fun o ↦ halg o p) (hend p)
  have hg := hmeasure branch (ec p) (endpointOutputMask f p output) (chartInputMask f p)
    _ backward (hRawSmooth backward (![1, 2, 3] branch)) ρ L 0 hL _ _
    (hgrades.2.1 branch) (hgrades.2.2 branch)
  have hcarrier : comparableJointCarrier 1 1 a b
      ((Prod.fst '' (tsupport (χo p) ×ˢ tsupport (χs p))) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      (tsupport (χo p) ×ˢ tsupport (χs p)) (frequencyAnnulus a b) ⊆
    comparableJointCarrier 1 1 a b
      ((Prod.fst '' (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))) ×ˢ
        frequencyAnnulus (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      (tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p))
      (frequencyAnnulus a b) := by
    intro v hv
    exact ⟨⟨hbase p hv.1.1, hv.1.2⟩,
      ⟨Set.image_mono (hbase p) hv.2.1, hv.2.2⟩⟩
  obtain ⟨Mi', Mo', hMi', hMo', hleak⟩ := hbnd p branch backward (mi p) (mo p)
    (hi p) (his p) (hirange p) (hom p) (hdiag p) (hann p) (hbasei p) (hbaseo p)
    (hmo p) ρ L hL hLρ
  have hei : Mi' = Mi := eq_of_rightLocalizer_representatives ρ (mi p) Mi' Mi hMi' hMi
  have heo : Mo' = Mo := eq_of_leftLocalizer_representatives ρ (mo p) Mo' Mo hMo' hMo
  subst Mi'
  subst Mo'
  have h := hleak
    (fun y idx ↦ (coefficient (f.chart p).index Q y idx).map Complex.ofReal)
    (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) (W p 1)
    (conicBminus (f.chart p).radialSection (f.chart p).index Q
      (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
      (f.chart p).row (f.chart p).col)
    (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) (![1, 2, 3] branch)
    (hAsmooth backward _) (fun k v hv ↦ hg.1 k v (hcarrier hv))
    (fun y _ k v _ ↦ by simpa only [hinProf, hio] using hinput L hL p branch y k v)
    (fun low j ξ hξ z hz k ↦ hg.2 low j ξ hξ z (hbase p hz) k)
    (by simpa only [houtProf, hoo] using houtput L hL p branch)
    (tsupport (selectedEndpointMultiplier f p threshold)) hF hzero
    (hsupport backward _) complexPhysicalCutoff (fun _ _ _ ↦ rfl)
    (Preg backward (![1, 2, 3] branch)) (hreal backward _) (hlim backward _) N u
  have heq : directPDOSymbols
      (fun y idx ↦ (coefficient (f.chart p).index Q y idx).map Complex.ofReal)
      (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) (W p 1)
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) (![1, 2, 3] branch) =
        ![selectedSourceSymbol f p (2*threshold),
          selectedEndpointSymbol f p threshold Q (W p 1),
          selectedAlgebraicSymbol f p (2*threshold) Q B 1] branch := by
    rw [selected_directPDOSymbols_eq_four_selected_symbols]
    fin_cases branch <;> rfl
  have hPeq := hP (![1, 2, 3] branch)
  rw [heq] at hPeq
  have hTop : Top = (if backward then
      (maskedPhysicalPDO (χo p) (χs p)
        (![selectedSourceSymbol f p (2*threshold),
          selectedEndpointSymbol f p threshold Q (W p 1),
          selectedAlgebraicSymbol f p (2*threshold) Q B 1] branch)).adjoint
      else maskedPhysicalPDO (χo p) (χs p)
        (![selectedSourceSymbol f p (2*threshold),
          selectedEndpointSymbol f p threshold Q (W p 1),
          selectedAlgebraicSymbol f p (2*threshold) Q B 1] branch)) := by
    exact congrArg (fun Dop : Hspace →L[ℂ] Hspace ↦ if backward then Dop.adjoint else Dop) hPeq
  rw [hTop]
  simpa only [heq, max_self, zero_add] using h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
