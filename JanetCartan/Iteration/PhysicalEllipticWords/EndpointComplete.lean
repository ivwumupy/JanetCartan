module

public import JanetCartan.Iteration.PhysicalEllipticWords.EndpointProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.Complete
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.ChartMasks
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.Endpoint

/-!
# Complete original endpoint letter, including its full-frequency complement

This is the concrete endpoint-symbol application, not a bound assumed for a
PDO. The original `W₁` and `EndpointPdoEstimates` certificates produce the near
amplitude and the full tail. `Coefficients`, `Phase` and `GradientBand` supply
the actual physical-history primitive profiles; task13 supplies the literal
reserved source Fourier profile. Both adjoints keep the original operator.
Consumer: the endpoint letters of `app:ch_response:eq:response-graded-reduced`.
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

variable {d : ℕ} {I ι : Type} [Fintype ι]
  {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
  {K₀ : Set (Euclidean (d + 1))}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "CW" => CarrierVariables (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
local notation "F" => EuclideanSpace ℂ (Fin (d + 1))

/-- The complete SAME endpoint PDO preserves the natural reserved source
power. No near/tail response, normalized-symbol profile, or final operator bound
is a hypothesis; those are derived from the original retained inverse data. -/
theorem endpoint_complete_reserved_ordered_bounds
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
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let g := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y, q)) c w
      ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ Csource l s * Adata i * K i ^ (s + l - Rsource)) :
    ∀ adj : Bool,
    let g := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold (Q i) (Ws i p))))
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
  obtain ⟨Aamp, hAamp, hamp⟩ := exists_selected_endpoint_reserved_joint_profiles
    f hΩ hball threshold ht hft output ho hoc hout hbuffer hmask ra rb hcoverage
      π hπ hcπ hzero AQ AB cost hAQ hAB hcost
  obtain ⟨Bsymbol, hBsymbol, htail⟩ := exists_selected_endpoint_tail_symbol_profiles
    f p output hout threshold Dsymbol AQ AB hDsymbol hAQ hAB
  let σ := fun i ↦ selectedEndpointSymbol f p threshold (Q i) (Ws i p)
  let σa := fun i y ξ ↦ endpointOutputMask f p output y • σ i y ξ
  have htail' i := htail Rcoef (by omega) (L i) (hL i) (Q i) (B i) (Ws i p)
    (hQp i) (hBp i) (Rnormal i) (Dgain i) (Ggain i) (hcertificate i)
  have hshape i : (fun y z ξ ↦ (chartInputMask f p y * chartInputMask f p z) •
      (π ((lam i)⁻¹ • ξ) • σa i y ξ)) =
      fun y z ξ ↦ π ((lam i)⁻¹ • ξ) • orientedMaskedPDOAmplitude false
        (endpointOutputMask f p output) (chartInputMask f p) (σ i) y z ξ := by
    funext y z ξ
    rw [smul_comm]
    congr 1
    exact absorbed_selected_amplitude_eq f p output hout (σ i) y z ξ
  have hnear i (adj : Bool) := hamp Rorig Rcoef hRcoef (L i) (lam i) (hL i) (hlam i)
    (Q i) (hQ i) (B i) (hQp i) (hBp i) (Ws i) (hW i) (hbudget i) p adj
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
