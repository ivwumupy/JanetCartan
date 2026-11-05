module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.ReservedNear
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.ComplementSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticResidualEnvelopes.AnnularRegularity
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.PdoReassembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Coordinates

/-!
# Restore every complementary frequency of the selected PDO

The complete source kernel uses the original full symbol. Its retained normal
certificate identifies the complementary integral with the exact difference
of the same full and annular bounded operators. Arbitrary complementary
precision retains the natural source reserve when that full PDO is restored.
The concrete endpoint and algebraic applications produce both primitive
symbol inputs from their original retained certificates.

Consumer: complete finite-letter estimates in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open ResponseTransfer ResponseTransfer.FullSourceEnvelopes ResponseTransfer.FullEllipticResidualEnvelopes
open ResponseTransfer.Complement ResponseTransfer.DirectEvolution
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open RegularSector.Characteristic.PdoRealization
open CharacteristicTransport.CompleteResidual ResponseTransfer.NearCarrierFullLow
open FixedDomainInverse.FiniteResidualEnvelopes
variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The same full PDO preserves the original source reserve, including the
literal adjoint and every complementary frequency. The inputs are primitive
symbol/phase/source jets and the original bounded realization certificate;
no response-output estimate is assumed
(`app:ch_response:eq:response-graded-reduced`). -/
theorem selected_pdo_complete_reserved_ordered_bounds
    (x : E) (radius : ℝ) (hradius : 0 < radius) (χout χsource : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ ball x radius)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (Aphase Aamp Bsymbol : ℕ → ℝ)
    (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j) (hBsymbol : ∀ j, 0 ≤ Bsymbol j)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (symbol : I → E → E → Mat)
    (hσ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (symbol i)))
    (hσjets : ∀ i j ξ y, ‖iteratedFDeriv ℝ j (fun z ↦ symbol i z ξ) y‖ ≤ Bsymbol j * L i ^ j)
    (hnormal : ∀ i, ∃ R N,
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource (symbol i)) R N)
    (hsymbol : ∀ i (adj : Bool),
      let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦ (χout y * χsource z) •
        (annularSelector (a₀/2) (2*B₀) (by positivity) (by positivity) ((lam i)⁻¹ • ξ) • symbol i y ξ)
      let α := fun (q : E × Par) (w : W) ↦ (lam i ^ (-1 : ℤ))⁻¹ •
        normalizedFullAmplitude (if adj then exchangedAdjointAmplitude A else A)
          (lam i) (q.1,w.fst,w.snd)
      ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ j v,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) v‖ ≤ Aamp j * L i ^ (j+2-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x radius ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x radius ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hsourceBand : ∀ i c, c ∈ V → ∀ y ∈ ball x radius,
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x radius)
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    ∀ adj : Bool,
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (symbol i)))
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
  intro adj output
  let X₀ := closedBall x radius
  have hX₀ : IsCompact X₀ := isCompact_closedBall _ _
  let : CompactSpace X₀ := isCompact_iff_compactSpace.mp hX₀
  have hmask' : tsupport χout ∪ tsupport χsource ⊆ X₀ :=
    hmask.trans ball_subset_closedBall
  have hRone : 1 ≤ Rstar := by omega
  let φ' := fun i c y ↦ φ i y c
  let a' := fun i c y ↦ a i (y,c)
  have hφ' i : ContDiff ℝ ∞ (Function.uncurry (φ' i)) :=
    (hφ i).comp (contDiff_snd.prodMk contDiff_fst)
  have hcφ i c : Continuous (φ' i c) :=
    (hφ i).continuous.comp (continuous_id.prodMk continuous_const)
  have hpoints (y : E) (hy : y ∈ S ∪ X₀) : y ∈ closedBall x radius := by
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
    hν hν1 ha₀ hB₀ χout χsource ho hs hmask'
    Bsymbol Aphase (fun k ↦ Aphase (k+1)) (fun l s ↦ max (Csource l s) 0)
    hBsymbol hAphase (fun k ↦ hAphase (k+1))
    lam L K Adata hlam hL hLK hscale hAdata symbol φ' a' hσ
    (fun i k ξ y _ ↦ hσjets i k ξ y) hnormal
    hφ' hφcoarse hsourceBand hsourceφ ha' has' hfourierWeak adj true
  let R := fun i ↦ completeDiagonalAnnularRemainder hX₀ adj true (symbol i)
    χout χsource π (φ' i) (lam i) (a' i)
  have hRsm : ∀ i, ContDiffOn ℝ ∞ (R i) V := htail.2.1
  have hnearSm i : ContDiffOn ℝ ∞ (fun c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource
        (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • symbol i y ξ))) (u i c)) V :=
    contDiffOn_complete_diagonal_annular_envelope hV hS hX₀ χout χsource ho hs hmask'
      (symbol i) (hσ i) (fun ξ ↦ π ((lam i)⁻¹ • ξ))
      (contDiff_physicalAnnularSelector _ _ _ _ (lam i))
      (hasCompactSupport_physicalAnnularSelector _ _ _ _ (zero_lt_one.trans_le (hlam i)))
      (φ' i) (hφ' i) (hcφ i) (lam i) (a' i) (ha' i) (has' i) (u i) (hu i) adj
  have hnear := selected_pdo_annular_reserved_ordered_bounds x radius hradius χout χsource
    hoc hsc hmask (by positivity : 0 < a₀/2) (by positivity : 0 < 2*B₀) basis hV hKpar hVK
    Rsource Rstar hRstar Aphase Aamp hAphase hAamp lam L K Adata hlam hL hLK hAdata
    symbol hsymbol φ hφ hcap hφjets S hS a ha has Csource hfourier adj
  let full := fun i c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
    (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (symbol i))) (u i c)
  let near := fun i c ↦ demodulatedL2Operator (lam i) (φ' i c) (hcφ i c)
    (annularGraphOrientation adj (maskedPhysicalPDO χout χsource
      (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • symbol i y ξ))) (u i c)
  have hnear' : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c) ≤
            C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
    intro ps hps s
    simpa only [near,π,Complex.coe_smul] using hnear ps hps s
  have hsum i c (hc : c ∈ V) : full i c = near i c+R i c := by
    have he := remainder_eq_demodulated_difference_of_ae
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (symbol i)))
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource
        (fun y ξ ↦ π ((lam i)⁻¹ • ξ) • symbol i y ξ))) (lam i) (φ' i c) (hcφ i c)
      (a' i c) (u i c) (R i c) (hu i c hc)
      (by simpa only [ite_true] using htail.2.2.2.2.1 i c hc)
    change R i c = full i c-near i c at he
    rw [he]
    abel
  exact ordered_reserved_bounds_of_annular_remainder full near R hV hsum hnearSm hRsm
    lam Adata K (-1) Rsource hlam hAdata (fun i ↦ (hL i).trans (hLK i)) hnear' htail.2.2.2.2.2

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
