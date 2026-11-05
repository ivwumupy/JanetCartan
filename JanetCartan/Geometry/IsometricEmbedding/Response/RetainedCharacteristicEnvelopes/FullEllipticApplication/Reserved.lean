module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.ReservedAnnular
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.Certification
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.ComplementSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.AnnularRegularity
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PdoReassembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates

/-!
# Complete elliptic envelopes with the original natural source reserve

Only the near part uses finite scale compression. The complementary integral
keeps the actual full symbol and the original scale; its arbitrary precision
preserves the low-order plateau when the complete operator is restored.
The coefficient reserve is spent only in the finite symbol and phase jets.

Consumer: naturally reserved finite residual words in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap

namespace JanetCartan.ResponseTransfer.FullEllipticApplication

open DiagonalPdo FullSourceEnvelopes FullEllipticResidualEnvelopes
open JanetCartan.ResponseTransfer.Complement
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open RegularSector.Characteristic.PdoRealization
open CharacteristicTransport.CompleteResidual
open FixedDomainInverse.FiniteResidualEnvelopes

variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

/-- The same complete selected inverse and residual retain the exact
naturally truncated source reserve, including every complementary frequency
and both literal adjoints. No negative slow-scale power is extracted from the
source amplitude (`app:ch_response:eq:response-graded-reduced`). -/
theorem complete_elliptic_reserved_ordered_bounds
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    (threshold : ℝ) (ht : fam.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall Aref fam.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hsourceBand : ∀ i c, c ∈ V → ∀ y ∈ ball x (3*fam.physicalRadius),
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*fam.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    ∀ residual adj : Bool,
    let σ := fun i y ξ ↦
      if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
        else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout (fun y ↦ (fam.inputMask y : ℂ)) (σ i)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    (∀ i, ContDiffOn ℝ ∞ (output i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
            C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
  classical
  intro residual adj σ output
  let χsource := fun y ↦ (fam.inputMask y : ℂ)
  let X₀ := closedBall x (3*fam.physicalRadius)
  have hX₀ : IsCompact X₀ := isCompact_closedBall _ _
  let : CompactSpace X₀ := isCompact_iff_compactSpace.mp hX₀
  have hχsource : ContDiff ℝ ∞ χsource := Complex.ofRealCLM.contDiff.comp fam.inputMask_smooth
  have hmask : tsupport χsource ∪ tsupport χsource ⊆ X₀ := by
    intro y hy
    rcases hy with hy | hy <;>
      exact ball_subset_closedBall (fam.inputMask_support (tsupport_comp_subset Complex.ofReal_zero fam.inputMask hy))
  let σa := fun i y ξ ↦ χout y • σ i y ξ
  obtain ⟨Bsymbol,hBsymbol,hposition⟩ := exists_complete_elliptic_masked_position_profiles
    fam hK₀ hΩcoeff hball χout ho hos AQ AB hAQ hAB
  have hRone : 1 ≤ Rstar := by omega
  have hposition' i := hposition threshold ht Rstar hRone (L i) (hL i) (Q i) (B i)
    (hQ i) (hB i) (hmap i)
    ((cNorm_mono_order (by omega : 1 ≤ 2*(d+2)+2)).trans (hQl i))
    ((cNorm_mono_order (Nat.zero_le _)).trans (hBl i)) (hQp i) (hBp i) residual
  have hσa i : ContDiff ℝ ∞ (Function.uncurry (σa i)) := (hposition' i).1
  have hσajet i k ξ y (_hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (fun z ↦ σa i z ξ) y‖ ≤ Bsymbol k * L i ^ k := (hposition' i).2 k ξ y
  obtain ⟨Rnormal,hRnormal,Mnormal,hMnormal,hnormal⟩ :=
    exists_complete_elliptic_absorbed_normal_certificates fam hK₀ hΩcoeff hball χout ho hoc hos
  have hnormal' i : ∃ R N,
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χsource χsource (σa i)) R N :=
    ⟨Rnormal,Mnormal,hnormal threshold ht (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) residual⟩
  let φ' := fun i c y ↦ φ i y c
  let a' := fun i c y ↦ a i (y,c)
  have hφ' i : ContDiff ℝ ∞ (Function.uncurry (φ' i)) :=
    (hφ i).comp (contDiff_snd.prodMk contDiff_fst)
  have hcφ i c : Continuous (φ' i c) :=
    (hφ i).continuous.comp (continuous_id.prodMk continuous_const)
  have hpoints (y : E) (hy : y ∈ S ∪ X₀) : y ∈ closedBall x (3*fam.physicalRadius) := by
    rcases hy with hy | hy
    · exact ball_subset_closedBall (hSU hy)
    · exact hy
  have hφcoarse i k c (hc : c ∈ V) y (hy : y ∈ S ∪ X₀) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (φ' i)) (c,y)‖ ≤ Aphase k * L i ^ k := by
    have he := (LinearIsometryEquiv.prodComm ℝ Par E).norm_iteratedFDeriv_comp_right
      (Function.uncurry (φ i)) (c,y) k
    apply he.le.trans
    exact (hφjets i k (y,c) ⟨hpoints y hy,hVK hc⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (Nat.sub_le k Rstar)) (hAphase k))
  have hsourceφ i c (hc : c ∈ V) y (hy : y ∈ S) k (_hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ (k+1) (φ' i c) y‖ ≤ Aphase (k+1) * L i ^ k := by
    have hs := ResponsePrimarySources.norm_iteratedFDeriv_primary_spatialSlice_le
      isOpen_univ isOpen_univ (a := Function.uncurry (φ i)) (hφ i).contDiffOn
      (mem_univ y) (mem_univ c) (k+1)
    exact (hs.trans (hφjets i (k+1) (y,c) ⟨ball_subset_closedBall (hSU hy),hVK hc⟩)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hL i) (by omega : k+1-Rstar ≤ k)) (hAphase (k+1)))
  have ha' i : ContDiffOn ℝ ∞ (Function.uncurry (a' i)) (V ×ˢ univ) :=
    ((ha i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have has' i c (_hc : c ∈ V) : tsupport (a' i c) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra h
    exact hy (has i (y,c) h)
  let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
  have hu i c (_hc : c ∈ V) : u i c =ᵐ[volume] a' i c :=
    vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c
  let π : E → ℂ := fun η ↦ annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) η
  have hfourierWeak : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
          max (Csource l s) 0 * Adata i * K i ^ (s+l) := by
    intro i c hc l w hw s f
    obtain ⟨hm,hmem,hbound⟩ := hfourier i c hc l w hw s
    refine ⟨hm,hmem,hbound.trans ?_⟩
    have hK : 1 ≤ K i := (hL i).trans (hLK i)
    calc
      Csource l s * Adata i * K i ^ (s+l-Rsource) ≤
          max (Csource l s) 0 * Adata i * K i ^ (s+l-Rsource) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left (Csource l s) 0) (hAdata i))
          (pow_nonneg (zero_le_one.trans hK) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hK (Nat.sub_le _ _))
        (mul_nonneg (le_max_right _ _) (hAdata i))
  have htail := completeDiagonalAnnularComplement_sobolev
    (EuclideanSpace.finAddEquivProd : Euclidean (3+d) ≃L[ℝ] Par)
    fullSource_coordinate_norm_bounds.1 hV hX₀ hS isOpen_ball isOpen_univ hSU (subset_univ _)
    hν hν1 ha₀ hB₀ χsource χsource hχsource hχsource hmask
    Bsymbol Aphase (fun k ↦ Aphase (k+1)) (fun l s ↦ max (Csource l s) 0) hBsymbol hAphase (fun k ↦ hAphase (k+1))
    lam L K Adata hlam hL hLK hscale hAdata σa φ' a' hσa hσajet hnormal'
    hφ' hφcoarse hsourceBand hsourceφ ha' has' hfourierWeak adj true
  let R := fun i ↦ completeDiagonalAnnularRemainder hX₀ adj true (σa i)
    χsource χsource π (φ' i) (lam i) (a' i)
  have hRsm : ∀ i, ContDiffOn ℝ ∞ (R i) V := htail.2.1
  have hnearSm i : ContDiffOn ℝ ∞ (fun c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
      (annularGraphOrientation adj (maskedPhysicalPDO χsource χsource
        (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σa i y ξ))) (u i c)) V := by
    exact contDiffOn_complete_diagonal_annular_envelope hV hS hX₀ χsource χsource
      hχsource hχsource hmask (σa i) (hσa i) (fun ξ ↦ π ((lam i)⁻¹ • ξ))
      (contDiff_physicalAnnularSelector _ _ _ _ (lam i))
      (hasCompactSupport_physicalAnnularSelector _ _ _ _ (zero_lt_one.trans_le (hlam i)))
      (φ' i) (hφ' i) (hcφ i) (lam i) (a' i) (ha' i) (has' i) (u i) (hu i) adj
  have hfullEq i : maskedPhysicalPDO χsource χsource (σa i) =
      maskedPhysicalPDO χout χsource (σ i) :=
    maskedPhysicalPDO_inputMask_output_absorption fam χout hos (σ i)
  have hcutEq i : maskedPhysicalPDO χsource χsource (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σa i y ξ) =
      maskedPhysicalPDO χout χsource (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σ i y ξ) := by
    have he : (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σa i y ξ) =
        fun y ξ ↦ χout y • (π ((lam i)⁻¹ • ξ) • σ i y ξ) := by
      funext y ξ
      exact smul_comm _ _ _
    rw [he]
    exact maskedPhysicalPDO_inputMask_output_absorption fam χout hos _
  have hnear := selected_elliptic_annular_reserved_ordered_bounds fam hK₀ hΩcoeff hball χout ho hoc hos
    threshold (fam.radialThreshold_ge_one.trans ht) (by positivity : 0 < a₀/2) (by positivity : 0 < 2*B₀)
    basis hV hKpar hVK Rsource Rstar hRstar AQ AB Aphase hAQ hAB hAphase lam L K Adata
    hlam hL hLK hAdata Q B hQ hB hmap hQp hBp φ hφ hcap hφjets S hS a ha has Csource hfourier
    residual adj
  let full := fun i c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
    (annularGraphOrientation adj (maskedPhysicalPDO χsource χsource (σa i))) (u i c)
  let near := fun i c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
    (annularGraphOrientation adj (maskedPhysicalPDO χsource χsource
      (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σa i y ξ))) (u i c)
  have hnear' : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c) ≤
            C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
    intro ps hps s
    dsimp only [near]
    simp_rw [hcutEq]
    simpa only [π,Complex.coe_smul] using hnear ps hps s
  have hsum i c (hc : c ∈ V) : full i c = near i c+R i c := by
    have he := remainder_eq_demodulated_difference_of_ae
      (annularGraphOrientation adj (maskedPhysicalPDO χsource χsource (σa i)))
      (annularGraphOrientation adj (maskedPhysicalPDO χsource χsource
        (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • σa i y ξ))) (lam i) (φ' i c) (hcφ i c)
      (a' i c) (u i c) (R i c) (hu i c hc)
      (by simpa only [ite_true] using htail.2.2.2.2.1 i c hc)
    change R i c = full i c-near i c at he
    rw [he]
    abel
  have hresult := ordered_reserved_bounds_of_annular_remainder full near R hV hsum hnearSm hRsm
    lam Adata K (-1) Rsource hlam hAdata (fun i ↦ (hL i).trans (hLK i)) hnear' htail.2.2.2.2.2
  dsimp only [full] at hresult
  simpa only [hfullEq] using hresult

end JanetCartan.ResponseTransfer.FullEllipticApplication
