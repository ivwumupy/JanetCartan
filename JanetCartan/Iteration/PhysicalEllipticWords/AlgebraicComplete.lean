module

public import JanetCartan.Iteration.PhysicalEllipticWords.AlgebraicProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.Complete
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.ChartMasks
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.Algebraic
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.AlgebraicCertificates

/-!
# Complete original algebraic solver and residual letters

The original retained algebraic construction supplies the normal/coordinate
certificate via `exists_supplied_algebraic_tail_coordinate_certificates`.
Reserved joint profiles and full tail jets are derived for the SAME symbols;
then the complete near/tail theorem proves both literal adjoint orientations.
The physical history and source producers are `Coefficients`, `Phase`,
`GradientBand`, and task13's reserved Fourier source.
Consumer: the algebraic letters of `app:ch_response:eq:response-graded-reduced`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalEllipticWords
open ArbitraryAccuracy.SelectedLocalization ArbitraryAccuracy.ResidualLocalization
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo
open RegularSector.FiniteAlgebraic RegularSector.FiniteAssembly
open RegularSector.Characteristic RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.EvolutionIntegral
open CharacteristicTransport.CompleteResidual FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential AmplitudeBound
open ResponseTransfer ResponseTransfer.DirectEvolution ResponseTransfer.NearCarrierFullLow
open ResponseTransfer.FullSourceEnvelopes ResponseTransfer.FullEllipticResidualEnvelopes ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.AnnularComplement
open FixedDomainInverse.SelectedPdoEnvelopeApplication
open FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols

variable {d : ℕ} {I ι : Type} [Fintype ι]
  {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))

/-- Both complete algebraic entries preserve the exact reserved source power.
The only retained symbol certificate is the original inverse construction's
coordinate/normal certificate, not any response or near/tail estimate. -/
theorem algebraic_complete_reserved_ordered_bounds
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
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) :
    ∀ (o : Fin 2) (adj : Bool),
    let g := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    (∀ i, ContDiffOn ℝ ∞ (g i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ≤
          C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s + ps.length - Rsource) := by
  let π := annularSelector (n := d + 1) (alo / 2) (2 * ahi) (by positivity) (by positivity)
  have hπ : ContDiff ℝ ∞ π := contDiff_annularSelector ..
  have hcπ : HasCompactSupport π := hasCompactSupport_annularSelector ..
  have hzero : (0 : E) ∉ tsupport π := by
    intro hz
    have hh := (tsupport_annularSelector_subset (alo / 2) (2 * ahi) (by positivity) (by positivity) hz).1
    simp only [norm_zero] at hh
    linarith
  obtain ⟨Aamp, hAamp, hamp⟩ := FixedDomainInverse.ReservedAlgebraicSymbol.exists_selected_algebraic_joint_reserved_profiles
    f hΩ hRQ hball hc hdom threshold ht output ho hoc hout π hπ hcπ hzero AQ AB hAQ hAB
  obtain ⟨Bsymbol, hBsymbol, htail⟩ := exists_selected_algebraic_tail_symbol_profiles
    f p output ho hoc hout threshold Dsymbol AQ AB hDsymbol hAQ hAB
  intro o
  let σ := fun i ↦ selectedAlgebraicSymbol f p (2 * threshold) (Q i) (B i) o
  let σa := fun i y ξ ↦ endpointOutputMask f p output y • σ i y ξ
  have htail' i : ContDiff ℝ ∞ (Function.uncurry (σa i)) ∧
      (∀ k ξ y, ‖iteratedFDeriv ℝ k (fun z ↦ σa i z ξ) y‖ ≤ Bsymbol k * L i ^ k) ∧
      (∃ R N, GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartInputMask f p) (chartInputMask f p) (σa i)) R N) ∧
      maskedPhysicalPDO (chartInputMask f p) (chartInputMask f p) (σa i) =
        maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) (σ i) := by
    obtain ⟨R, N, hn, hcoord⟩ := hcertificate i o
    exact htail Rcoef (by omega) (L i) (hL i) (Q i) (B i) (hQp i) (hBp i) o R N hn hcoord
  have hshape i : (fun y z ξ ↦ (chartInputMask f p y * chartInputMask f p z) •
      (π ((lam i)⁻¹ • ξ) • σa i y ξ)) =
      fun y z ξ ↦ π ((lam i)⁻¹ • ξ) • orientedMaskedPDOAmplitude false
        (endpointOutputMask f p output) (chartInputMask f p) (σ i) y z ξ := by
    funext y z ξ
    rw [smul_comm]
    congr 1
    exact absorbed_selected_amplitude_eq f p output hout (σ i) y z ξ
  have hnear i (adj : Bool) := hamp Rorig Rcoef hRcoef (L i) (lam i) (hL i) (hlam i)
    (Q i) (B i) (hQ i) (hB i) (hmap i) (hQp i) (hBp i) p o adj
  obtain ⟨_, _hcs, hbox⟩ := selected_chart_pdo_masks_source_box f p output ho hoc hout
  have hmask' : tsupport (chartInputMask f p) ∪ tsupport (chartInputMask f p) ⊆
      ball ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius) := by
    intro y hy
    exact hbox (Or.inr (hy.elim id id))
  have hχ := (chartPhysicalMasks_properties f p).2.1
  have hcχ := (chartPhysicalMasks_properties f p).2.2.2.1
  have hresult := selected_pdo_complete_reserved_ordered_bounds
    ((physicalCoordinates (f.chart p).index).symm x) (3 * f.physicalRadius)
    (mul_pos (by norm_num) f.physicalRadius_pos)
    (chartInputMask f p) (chartInputMask f p) hχ hχ hcχ hcχ hmask'
    hν hν1 halo hahi basis hV hKpar hVK Rsource Rorig hRorig
    Aphase Aamp Bsymbol hAphase hAamp hBsymbol lam L K Adata hlam hL hLK hscale hAdata
    σa (fun i ↦ (htail' i).1) (fun i ↦ (htail' i).2.1) (fun i ↦ (htail' i).2.2.1)
    (fun i adj ↦ by simpa only [hshape i, σ, π] using hnear i adj)
    φ hφ hcap hφjets hband S hS hSU a ha has Csource hfourier
  intro adj
  simpa only [σa, maskedPhysicalPDO_chartInput_output_absorption f p output hout, σ] using hresult adj

end JanetCartan.PhysicalEllipticWords
