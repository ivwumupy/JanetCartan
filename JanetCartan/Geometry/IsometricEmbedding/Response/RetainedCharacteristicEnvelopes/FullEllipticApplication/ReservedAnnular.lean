module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.FiniteScale
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReserveCompression
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.ReservedMixedJets

/-!
# Preserve the exact natural reserve in the actual elliptic annular estimate

The original mixed source Fourier estimates and the actual elliptic amplitude
profiles are compressed only at a fixed total derivative order. The primitive
PDO theorem consumes exactly that finite range. The original scale and its
natural low-order plateau are restored at the output, with no extraction of a
negative power from the source amplitude.

Consumer: complete reserved elliptic envelopes in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap

namespace JanetCartan.ResponseTransfer.FullEllipticApplication

open JanetCartan.ResponseTransfer.Complement
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open CharacteristicTransport.CompleteResidual
open FixedDomainInverse FixedDomainInverse.FiniteResidualEnvelopes

variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

/-- The actual selected inverse and residual retain the naturally truncated
source reserve at every ordered derivative degree. All finite symbol, phase
and mixed datum estimates are produced from the original profiles; both
literal Hilbert orientations and the full independent source parameters are
retained (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_elliptic_annular_reserved_ordered_bounds
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    {ra rb : ℝ} (hra : 0 < ra) (hrb : 0 < rb)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall Aref fam.coefficientRadius))
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (S : Set E) (hS : IsCompact S)
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    let π := annularSelector (n := d+1) ra rb hra hrb
    ∀ residual adj : Bool,
    let σ := fun i y ξ ↦ π ((lam i)⁻¹ • ξ) •
      (if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
        else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ)
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout (fun y ↦ (fam.inputMask y : ℂ)) (σ i)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
            C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
  classical
  intro π residual adj σ output ps hps s
  let Knear := fun i ↦ reservedEnvelopeScale (K i) (s+ps.length) Rsource
  have hK i : 1 ≤ K i := (hL i).trans (hLK i)
  have hKnear i : 1 ≤ Knear i := one_le_reservedEnvelopeScale (hK i) (s+ps.length) Rsource
  have hphaseScale i j (hj : j ≤ fullLowReserve (d+1)+(s+ps.length)+2) :
      L i ^ (j-Rstar) ≤ Knear i ^ (j-(fullLowReserve (d+1)+3)) := by
    apply (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLK i) _).trans
    exact (pow_le_pow_right₀ (hK i) (by omega : j-Rstar ≤ (j-(fullLowReserve (d+1)+3))-Rsource)).trans
      (reserved_power_le_reservedEnvelopeScale (hK i) (by omega) Rsource)
  have hampScale i j (hj : j ≤ fullLowReserve (d+1)+(s+ps.length)) :
      L i ^ (j+2-Rstar) ≤ Knear i ^ (j+2-(fullLowReserve (d+1)+3)) := by
    apply (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLK i) _).trans
    exact (pow_le_pow_right₀ (hK i) (by omega : j+2-Rstar ≤ (j+2-(fullLowReserve (d+1)+3))-Rsource)).trans
      (reserved_power_le_reservedEnvelopeScale (hK i) (by omega) Rsource)
  let a' := fun i c y ↦ a i (y,c)
  have ha' i : ContDiffOn ℝ ∞ (Function.uncurry (a' i)) (V ×ˢ univ) :=
    ((ha i).comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have has' i c (_hc : c ∈ V) : tsupport (a' i c) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra h
    exact hy (has i (y,c) h)
  obtain ⟨Dprofile,hDprofile,hmixed⟩ := exists_fullSource_reserved_mixedL2_profile
    (d+1) d (d+1) Csource Rsource
  have hdatum := hmixed I V S hS hV a' Adata K ha' has' ha has hAdata hK
    (by
      intro i c hc l w hw j
      obtain ⟨hm,hmem,hbound⟩ := hfourier i c hc l w hw j
      exact hmem)
    (by
      intro i c hc l w hw j
      obtain ⟨hm,hmem,hbound⟩ := hfourier i c hc l w hw j
      exact hbound)
  have hcompressed i c (hc : c ∈ V) j (hj : j ≤ s+ps.length) :
      ∃ hm : MemLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c)) 2 volume,
        ‖hm.toLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c))‖ ≤
          Adata i * Dprofile j * Knear i ^ j := by
    obtain ⟨hm,hb⟩ := hdatum i c hc j
    exact ⟨hm,hb.trans (mul_le_mul_of_nonneg_left
      (reserved_power_le_reservedEnvelopeScale (hK i) hj Rsource)
      (mul_nonneg (hAdata i) (hDprofile j)))⟩
  obtain ⟨C,hC,hbound⟩ := elliptic_annular_sobolev_of_finite_scale_compression
    fam hK₀ hΩcoeff hball χout ho hoc hos threshold ht hra hrb basis s ps hps hV hKpar hVK
    Rstar (fullLowReserve (d+1)+3) (by omega) (by omega) AQ AB Aphase hAQ hAB hAphase
    lam L Knear Adata hlam hL hKnear hAdata Q B hQ hB hmap hQp hBp
    φ hφ hcap hφjets hphaseScale hampScale S hS a ha has Dprofile hDprofile hcompressed residual adj
  refine ⟨C,hC,?_⟩
  intro i c hc
  have hb := hbound i c hc
  have he : Knear i ^ (s+ps.length) = K i ^ (s+ps.length-Rsource) :=
    reservedEnvelopeScale_pow_top (hK i) (s+ps.length) Rsource
  simpa only [he] using hb

end JanetCartan.ResponseTransfer.FullEllipticApplication
