module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedOperations

/-!
# Actual normalized endpoint and algebraic chart letters

Apply the complete original PDO constructors to both source phases and to the
conjugate of the same datum. This constructs both halves of the actual normalized
pair, with the literal complex scalar and both adjoint orientations. No signed
response estimate is assumed. The physical measured alphabet is the consumer
(`app:ch_response:eq:response-graded-reduced`, `energy-complete-residual`).
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
open RegularSector.FiniteAssembly RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.AlgebraicChart AmplitudeBound

variable {d : ℕ} {I ι : Type} [Fintype ι]
  {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))

/-- Both actual whole-conjugate halves with the original complete endpoint operator, source and natural reserve. -/
theorem endpoint_paired_chart_reserved_bounds
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M) (p : f.centers)
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
        (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i k q, q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) q‖ ≤ Aphase k * L i ^ (k - Rorig))
    (hband : ∀ i c, c ∈ V → ∀ y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius),
      alo ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ ahi)
    (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) (z : ℂ) :
    ∀ adj : Bool,
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (normalizedPair (z • (annularGraphOrientation adj (maskedPhysicalPDO
          (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p))))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
  classical
  intro adj
  let raw := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO
          (endpointOutputMask f p output) (chartInputMask f p) (selectedEndpointSymbol f p threshold (Q i) (Ws i p)))
  let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
  have hforward : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const)) (raw i) (u i c))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [ReservedLetterBounds, raw, u, mul_assoc] using
      (endpoint_complete_reserved_ordered_bounds f p hΩ hball threshold ht hft
    output ho hoc hout hbuffer hmask ra rb hcoverage hν hν1 halo hahi basis
    hV hKpar hVK Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol cost
    hAQ hAB hAphase hDsymbol hcost lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hQp hBp Ws hW hbudget Rnormal Dgain Ggain hcertificate
        φ hφ hcap hφjets hband S hS hSU a ha has Csource hfourier adj)
  let φneg := fun i y c ↦ -φ i y c
  have hφneg i : ContDiff ℝ ∞ (Function.uncurry (φneg i)) := (hφ i).neg
  have hcapneg i : cNorm
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φneg i)) ≤ Aphase 2 := by
    change cNorm _ _ (-Function.uncurry (φ i)) ≤ _
    simpa only [cNorm_neg] using hcap i
  have hφnegjets i k q (hq : q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (φneg i)) q‖ ≤ Aphase k * L i ^ (k - Rorig) := by
    change ‖iteratedFDeriv ℝ k (-Function.uncurry (φ i)) q‖ ≤ _
    simpa only [iteratedFDeriv_neg_apply, norm_neg] using hφjets i k q hq
  have hbandneg i c (hc : c ∈ V) y (hy : y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius)) :
      alo ≤ ‖fderiv ℝ (fun w ↦ φneg i w c) y‖ ∧
        ‖fderiv ℝ (fun w ↦ φneg i w c) y‖ ≤ ahi := by
    change alo ≤ ‖fderiv ℝ (-(fun w ↦ φ i w c)) y‖ ∧
      ‖fderiv ℝ (-(fun w ↦ φ i w c)) y‖ ≤ ahi
    simpa only [fderiv_neg, norm_neg] using hband i c hc y hy
  let astar := fun i q ↦ star (a i q)
  have hastar i : ContDiff ℝ ∞ (astar i) :=
    (starL' ℝ : F ≃L[ℝ] F).contDiff.comp (ha i)
  have hsastar i q (hq : q.1 ∉ S) : astar i q = 0 := by
    simp only [astar, has i q hq, star_zero]
  obtain ⟨Cstar, _hCstar, hstar⟩ :=
    exists_conjugate_source_fourier_profiles (n := d + 1) (r := d + 1) («Par» := Euclidean 3 × Euclidean d) (I := I) Csource hCsource
  have hstar' := hstar a Adata K Rsource V hfourier
  have hdatumStar i c :
      graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c) = star (u i c) := by
    apply Lp.ext
    filter_upwards [vectorOriginalDatumTest_toLp_ae (astar i) (hastar i) hS (hsastar i) [] c,
      Lp.coeFn_star (u i c), vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c]
      with y hb hs hd
    change (star (u i c)) y = star ((u i c) y) at hs
    rw [show (u i c) y = a i (y, c) from hd] at hs
    exact hb.trans hs.symm
  have hnegative : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ -φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).neg (raw i) (star (u i c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [ReservedLetterBounds, raw, φneg, hdatumStar, mul_assoc] using
      (endpoint_complete_reserved_ordered_bounds f p hΩ hball threshold ht hft
    output ho hoc hout hbuffer hmask ra rb hcoverage hν hν1 halo hahi basis
    hV hKpar hVK Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol cost
    hAQ hAB hAphase hDsymbol hcost lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hQp hBp Ws hW hbudget Rnormal Dgain Ggain hcertificate
        φneg hφneg hcapneg hφnegjets hbandneg S hS hSU
        astar hastar hsastar Cstar hstar' adj)
  exact normalized_pair_reserved_bounds hV raw lam (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K
    (fun i c y ↦ φ i y c)
    (fun i c ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    u Rsource hforward hnegative z

/-- Both actual whole-conjugate halves with the original complete algebraic operator, source and natural reserve. -/
theorem algebraic_paired_chart_reserved_bounds
    (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K₀ M) (p : f.centers)
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
        (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i k q, q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ i)) q‖ ≤ Aphase k * L i ^ (k - Rorig))
    (hband : ∀ i c, c ∈ V → ∀ y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius),
      alo ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ ahi)
    (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) (z : ℂ) :
    ∀ (o : Fin 2) (adj : Bool),
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
        (normalizedPair (z • (annularGraphOrientation adj (maskedPhysicalPDO
          (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o)))))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
  classical
  intro o adj
  let raw := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO
          (endpointOutputMask f p output) (chartInputMask f p) (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o))
  let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
  have hforward : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const)) (raw i) (u i c))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [ReservedLetterBounds, raw, u, mul_assoc] using
      (algebraic_complete_reserved_ordered_bounds f p hΩ hRQ hball hc hdom threshold ht
    output ho hoc hout hν hν1 halo hahi basis hV hKpar hVK
    Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol hAQ hAB hAphase hDsymbol
    lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQp hBp hcertificate
        φ hφ hcap hφjets hband S hS hSU a ha has Csource hfourier o adj)
  let φneg := fun i y c ↦ -φ i y c
  have hφneg i : ContDiff ℝ ∞ (Function.uncurry (φneg i)) := (hφ i).neg
  have hcapneg i : cNorm
      (closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φneg i)) ≤ Aphase 2 := by
    change cNorm _ _ (-Function.uncurry (φ i)) ≤ _
    simpa only [cNorm_neg] using hcap i
  have hφnegjets i k q (hq : q ∈
      closedBall ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) ×ˢ Kpar) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (φneg i)) q‖ ≤ Aphase k * L i ^ (k - Rorig) := by
    change ‖iteratedFDeriv ℝ k (-Function.uncurry (φ i)) q‖ ≤ _
    simpa only [iteratedFDeriv_neg_apply, norm_neg] using hφjets i k q hq
  have hbandneg i c (hc : c ∈ V) y (hy : y ∈
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius)) :
      alo ≤ ‖fderiv ℝ (fun w ↦ φneg i w c) y‖ ∧
        ‖fderiv ℝ (fun w ↦ φneg i w c) y‖ ≤ ahi := by
    change alo ≤ ‖fderiv ℝ (-(fun w ↦ φ i w c)) y‖ ∧
      ‖fderiv ℝ (-(fun w ↦ φ i w c)) y‖ ≤ ahi
    simpa only [fderiv_neg, norm_neg] using hband i c hc y hy
  let astar := fun i q ↦ star (a i q)
  have hastar i : ContDiff ℝ ∞ (astar i) :=
    (starL' ℝ : F ≃L[ℝ] F).contDiff.comp (ha i)
  have hsastar i q (hq : q.1 ∉ S) : astar i q = 0 := by
    simp only [astar, has i q hq, star_zero]
  obtain ⟨Cstar, _hCstar, hstar⟩ :=
    exists_conjugate_source_fourier_profiles (n := d + 1) (r := d + 1) («Par» := Euclidean 3 × Euclidean d) (I := I) Csource hCsource
  have hstar' := hstar a Adata K Rsource V hfourier
  have hdatumStar i c :
      graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c) = star (u i c) := by
    apply Lp.ext
    filter_upwards [vectorOriginalDatumTest_toLp_ae (astar i) (hastar i) hS (hsastar i) [] c,
      Lp.coeFn_star (u i c), vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c]
      with y hb hs hd
    change (star (u i c)) y = star ((u i c) y) at hs
    rw [show (u i c) y = a i (y, c) from hd] at hs
    exact hb.trans hs.symm
  have hnegative : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ -φ i y c)
        ((hφ i).continuous.comp (continuous_id.prodMk continuous_const)).neg (raw i) (star (u i c)))
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K Rsource := by
    simpa only [ReservedLetterBounds, raw, φneg, hdatumStar, mul_assoc] using
      (algebraic_complete_reserved_ordered_bounds f p hΩ hRQ hball hc hdom threshold ht
    output ho hoc hout hν hν1 halo hahi basis hV hKpar hVK
    Rsource Rorig Rcoef hRorig hRcoef AQ AB Aphase Dsymbol hAQ hAB hAphase hDsymbol
    lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQp hBp hcertificate
        φneg hφneg hcapneg hφnegjets hbandneg S hS hSU
        astar hastar hsastar Cstar hstar' o adj)
  exact normalized_pair_reserved_bounds hV raw lam (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K
    (fun i c y ↦ φ i y c)
    (fun i c ↦ (hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    u Rsource hforward hnegative z

end JanetCartan.PhysicalEllipticWords
