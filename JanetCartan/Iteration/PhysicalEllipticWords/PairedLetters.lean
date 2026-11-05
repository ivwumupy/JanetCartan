module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedCharts
public import JanetCartan.Iteration.PhysicalEllipticWords.PairedTransfer
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.CharacteristicCosts

/-!
# Actual endpoint and algebraic steps of the measured residual alphabet

These are the exact endpoint/algebraic `hstep` inputs for
`actual_finite_residual_word_reserved_bounds_of_one_step`. The same complete
PDO, external half, whole conjugate, full B, source and measurement masks are
retained. Both signed chart bounds, the physical source Fourier profile and
the fixed output multiplier estimate are constructed by the preceding leaves.
No bound for a paired/measured response or intermediate word is a premise.
Original retained inverse and physical-history data instantiate the explicit
primitive coefficient/phase/source inputs in the parent construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalEllipticWords
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo
open RegularSector.FinitePdo.RetainedConstruction RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open CharacteristicTransport.CompleteResidual FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open ResponseTransfer ResponseTransfer.DirectEvolution ResponseTransfer.NearCarrierFullLow
open ResponseTransfer.FullSourceEnvelopes ResponseTransfer.FullEllipticResidualEnvelopes ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.AnnularComplement
open FixedDomainInverse.SelectedPdoEnvelopeApplication
open FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
open FixedDomainInverse.FiniteResidualEnvelopes RegularSector.NormalizedSolver
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.AlgebraicChart AmplitudeBound

variable {d : ℕ} {I ι : Type} [Fintype ι]
  {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))

open RegularSector.Realization RegularSector.FiniteEvolution
open RegularSector.FiniteResidual.FiniteIdentity RegularSector.FiniteAssembly
local notation "H" => Lp F 2 (volume : Measure E)

/-- The actual endpoint branch of the SAME complete measured residual alphabet; exact natural source reserve, no response-bound hypothesis. -/
theorem endpoint_paired_measured_word_bounds
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M) (p : f.centers) (hK₀ : IsCompact K₀)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius / 2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    {ν alo ahi : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (halo : 0 < alo) (hahi : 0 < ahi)
    (basis : OrthonormalBasis ι ℝ CW)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rorig Rcoef : ℕ) (hRorig : Rsource + fullLowReserve (d + 1) + 3 ≤ Rorig)
    (hRcoef : Rorig + 10 ≤ Rcoef)
    (AQ AB Aphase Dsymbol : ℕ → ℝ) (cost : f.centers → ℕ → ℝ)
    (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) (hAphase : ∀ k, 0 ≤ Aphase k)
    (hDsymbol : ∀ k, 0 ≤ Dsymbol k) (hcost : ∀ p k, 0 ≤ cost p k)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat) (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω)
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i ^ (k - Rcoef))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i ^ (k - Rcoef))
    (Ws : I → f.centers → TwoTimeAmplitude d (d + 1))
    (hW : ∀ i p, ContDiff ℝ ∞ (jointAmplitude (Ws i p)))
    (hbudget : ∀ i p k,
      let e := coordinateSplit (f.chart p).index
      let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
      let J := bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius / 2) (ra p) (rb p)
      BoundedTwoTimeOrderSeminorm 1 J k (Ws i p) ∧
        twoTimeOrderSeminorm 1 J k (Ws i p) ≤ cost p k *
          (1 + cNorm (closedBall x RQ) (k + 10) (Q i) + cNorm (closedBall x RQ) (k + 9) (B i)))
    (Rnormal : I → ℝ) (Dgain Ggain : I → ℕ → ℝ)
    (hcertificate : ∀ i, EndpointPdoEstimates (f.chart p).index (closedBall x RQ) (Q i) (B i)
      (endpointOutputMask f p output) (chartInputMask f p)
      (selectedEndpointSymbol f p threshold (Q i) (Ws i p)) (Rnormal i) M Dsymbol (Dgain i) (Ggain i))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) 2
        (Function.uncurry (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) ≤ Aphase 2)
    (hφjets : ∀ i k q, q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ k (Function.uncurry (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) q‖ ≤ Aphase k * L i ^ (k - Rorig))
    (hband : ∀ i c, c ∈ V → ∀ y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius),
      alo ≤ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ≤ ahi)
    (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ ball x (3 * f.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) 
    (χout χin : E → ℝ) (hχout : ContDiff ℝ ∞ χout) (hcχout : HasCompactSupport χout)
    (hχin : Continuous χin) (hbχout : ∀ y, ‖χout y‖ ≤ 1) (hbχin : ∀ y, ‖χin y‖ ≤ 1)
    (hplateau : ∀ y ∈ S, χin y = 1)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (retarded : I → f.centers → H →L[ℂ] H) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (measuredOperator χout χin hχout.continuous hχin hbχout hbχin
          (selectedFullPairedResidualTerm f hK₀ threshold (Q i) (B i) (Ws i)
            output ho.continuous hob hib (retarded i) (Sum.inl (p, 0))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) Adata K Rsource := by
  let index := (f.chart p).index
  let φc := fun i y c ↦ φ i (physicalCoordinates index y) c
  have hφc i : ContDiff ℝ ∞ (Function.uncurry (φc i)) :=
    (hφ i).comp (((physicalCoordinates index).contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let ac := fun i ↦ pairedChartSource index (a i)
  have hac i : ContDiff ℝ ∞ (ac i) := pairedChartSource_smooth index (a i) (ha i)
  let Sc := physicalCoordinates index ⁻¹' S
  have hSc : IsCompact Sc := (physicalCoordinates index).toHomeomorph.isCompact_preimage.mpr hS
  have hasc i q (hq : q.1 ∉ Sc) : ac i q = 0 :=
    pairedChartSource_supported index (a i) S (has i) q hq
  have hScU : Sc ⊆ ball ((physicalCoordinates index).symm x) (3 * f.physicalRadius) :=
    pairedChartSource_ball index hSU
  have hsource := pairedChartSource_fourier index a Adata K Rsource V Csource hfourier
  have hp := endpoint_paired_chart_reserved_bounds f p hΩ hball threshold ht hft
    output ho hoc hout hbuffer hmask ra rb hcoverage hν hν1 halo hahi basis
    hV hKpar hVK Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol cost
    hAQ hAB hAphase hDsymbol hcost lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hQp hBp Ws hW hbudget Rnormal Dgain Ggain hcertificate
    φc hφc hcap hφjets hband Sc hSc hScU ac hac hasc Csource hCsource hsource (1 : ℂ) false
  let T := fun i ↦ normalizedPair ((1 : ℂ) • (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p))))
  have htest i c : graphTestToLp (vectorOriginalDatumTest (ac i) (hac i) hSc (hasc i) [] c) =
      physicalPullbackL2 index (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) :=
    pairedChartSource_test_eq index (a i) (ha i) S hS (has i) c
  have hchart : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i)
        (fun y ↦ φ i (physicalCoordinates index y) c)
        (((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).comp
          (physicalCoordinates index).continuous) (T i)
        (physicalPullbackL2 index
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [T, φc, htest, annularGraphOrientation,
      Bool.false_eq_true, ↓reduceIte] using hp
  have hm := measured_physical_reserved_bounds hV index T lam
    (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource φ
    (fun i c ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    S hS a ha has χout χin hχout hcχout hχin hbχout hbχin hplateau hchart
  have he i : physicalOperator index (T i) =
      selectedFullPairedResidualTerm f hK₀ threshold (Q i) (B i) (Ws i)
        output ho.continuous hob hib (retarded i) (Sum.inl (p, 0)) := by
    rw [selectedFullPairedResidualTerm_characteristic]
    dsimp only [T]
    rw [one_smul]
    change physicalOperator index (normalizedPair (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p)))) =
      normalizedPair (physicalOperator index (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p))))
    simpa only [one_smul] using
      physicalOperator_normalized_scalar_pair index (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p))) (1 : ℂ)
  have hfinal := hm.discard_inverse_frequency hlam hAdata
    (fun i ↦ zero_le_one.trans ((hL i).trans (hLK i)))
  simpa only [he] using hfinal

/-- The actual algebraic branch of the SAME complete measured residual alphabet; exact natural source reserve, no response-bound hypothesis. -/
theorem algebraic_paired_measured_word_bounds
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M) (p : f.centers) (hK₀ : IsCompact K₀)
    (hΩ : IsOpen Ω) (hRQ : 0 ≤ RQ) (hball : closedBall x RQ ⊆ Ω)
    (hc : ∀ p : f.centers,
      let c := f.chart p
      RootBuffer c.index c.row c.col (cubeStress (d + 1)) p.val.val c.root
        c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    (hdom : ∀ p : f.centers, ∀ A' : Coeff, A' ∈ closedBall (cubeStress (d + 1)) f.coefficientRadius →
      let c := f.chart p
      (physicalCoordinates c.index ⁻¹' Ω) ×ˢ
        (normalizeCovector c.radialSection '' tsupport
          (selectedEndpointMultiplier f p f.radialThreshold)) ⊆
        complementDomain c.index (fun _ : E ↦ A')
          (fieldRoot (coordinateSplit c.index) (fun _ : E ↦ A') c.root) c.row c.col
          (normalizedRootDomain c))
    (threshold : ℝ) (ht : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hout : tsupport output ⊆ ball x f.physicalRadius)
    {ν alo ahi : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (halo : 0 < alo) (hahi : 0 < ahi)
    (basis : OrthonormalBasis ι ℝ CW)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rorig Rcoef : ℕ) (hRorig : Rsource + fullLowReserve (d + 1) + 3 ≤ Rorig)
    (hRcoef : Rorig + 10 ≤ Rcoef)
    (AQ AB Aphase Dsymbol : ℕ → ℝ)
    (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k) (hAphase : ∀ k, 0 ≤ Aphase k)
    (hDsymbol : ∀ k, 0 ≤ Dsymbol k)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1 - ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ω)
    (hmap : ∀ i, MapsTo (Q i) Ω (closedBall (cubeStress (d + 1)) f.coefficientRadius))
    (hQp : ∀ i k, cNorm (closedBall x RQ) k (Q i) ≤ AQ k * L i ^ (k - Rcoef))
    (hBp : ∀ i k, cNorm (closedBall x RQ) k (B i) ≤ AB k * L i ^ (k - Rcoef))
    (hcertificate : ∀ i (o : Fin 2), ∃ R N,
      GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o)) R N ∧
      ∀ k ξ is, is.length ≤ k → ∀ z,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o) ξ) z‖ ≤
          Dsymbol k * (1 + cNorm (closedBall x RQ) (k + 1) (Q i) + cNorm (closedBall x RQ) (k + 1) (B i)))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) 2
        (Function.uncurry (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) ≤ Aphase 2)
    (hφjets : ∀ i k q, q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ k (Function.uncurry (fun y c ↦ φ i (physicalCoordinates (f.chart p).index y) c)) q‖ ≤ Aphase k * L i ^ (k - Rorig))
    (hband : ∀ i c, c ∈ V → ∀ y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius),
      alo ≤ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i (physicalCoordinates (f.chart p).index z) c) y‖ ≤ ahi)
    (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ ball x (3 * f.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) 
    (χout χin : E → ℝ) (hχout : ContDiff ℝ ∞ χout) (hcχout : HasCompactSupport χout)
    (hχin : Continuous χin) (hbχout : ∀ y, ‖χout y‖ ≤ 1) (hbχin : ∀ y, ‖χin y‖ ≤ 1)
    (hplateau : ∀ y ∈ S, χin y = 1)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖f.inputMask y‖ ≤ 1)
    (Ws : I → f.centers → TwoTimeAmplitude d (d + 1))
    (retarded : I → f.centers → H →L[ℂ] H) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (measuredOperator χout χin hχout.continuous hχin hbχout hbχin
          (selectedFullPairedResidualTerm f hK₀ threshold (Q i) (B i) (Ws i)
            output ho.continuous hob hib (retarded i) (Sum.inl (p, 2))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) Adata K Rsource := by
  let index := (f.chart p).index
  let φc := fun i y c ↦ φ i (physicalCoordinates index y) c
  have hφc i : ContDiff ℝ ∞ (Function.uncurry (φc i)) :=
    (hφ i).comp (((physicalCoordinates index).contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let ac := fun i ↦ pairedChartSource index (a i)
  have hac i : ContDiff ℝ ∞ (ac i) := pairedChartSource_smooth index (a i) (ha i)
  let Sc := physicalCoordinates index ⁻¹' S
  have hSc : IsCompact Sc := (physicalCoordinates index).toHomeomorph.isCompact_preimage.mpr hS
  have hasc i q (hq : q.1 ∉ Sc) : ac i q = 0 :=
    pairedChartSource_supported index (a i) S (has i) q hq
  have hScU : Sc ⊆ ball ((physicalCoordinates index).symm x) (3 * f.physicalRadius) :=
    pairedChartSource_ball index hSU
  have hsource := pairedChartSource_fourier index a Adata K Rsource V Csource hfourier
  have hp := algebraic_paired_chart_reserved_bounds f p hΩ hRQ hball hc hdom threshold ht
    output ho hoc hout hν hν1 halo hahi basis hV hKpar hVK
    Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol hAQ hAB hAphase hDsymbol
    lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQp hBp hcertificate
    φc hφc hcap hφjets hband Sc hSc hScU ac hac hasc Csource hCsource hsource (1 / Complex.I : ℂ) 1 false
  let T := fun i ↦ normalizedPair ((1 / Complex.I : ℂ) • (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) 1)))
  have htest i c : graphTestToLp (vectorOriginalDatumTest (ac i) (hac i) hSc (hasc i) [] c) =
      physicalPullbackL2 index (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) :=
    pairedChartSource_test_eq index (a i) (ha i) S hS (has i) c
  have hchart : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i)
        (fun y ↦ φ i (physicalCoordinates index y) c)
        (((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).comp
          (physicalCoordinates index).continuous) (T i)
        (physicalPullbackL2 index
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [T, φc, htest, annularGraphOrientation,
      Bool.false_eq_true, ↓reduceIte] using hp
  have hm := measured_physical_reserved_bounds hV index T lam
    (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource φ
    (fun i c ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    S hS a ha has χout χin hχout hcχout hχin hbχout hbχin hplateau hchart
  have he i : physicalOperator index (T i) =
      selectedFullPairedResidualTerm f hK₀ threshold (Q i) (B i) (Ws i)
        output ho.continuous hob hib (retarded i) (Sum.inl (p, 2)) := by
    rw [selectedFullPairedResidualTerm_characteristic]
    change physicalOperator index (normalizedPair ((1 / Complex.I : ℂ) • (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) 1)))) =
      normalizedPair (physicalOperator index ((1 / Complex.I : ℂ) • (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) 1))))
    simpa only [one_smul] using
      physicalOperator_normalized_scalar_pair index ((1 / Complex.I : ℂ) • (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) 1))) (1 : ℂ)
  have hfinal := hm.discard_inverse_frequency hlam hAdata
    (fun i ↦ zero_le_one.trans ((hL i).trans (hLK i)))
  simpa only [he] using hfinal

end JanetCartan.PhysicalEllipticWords
