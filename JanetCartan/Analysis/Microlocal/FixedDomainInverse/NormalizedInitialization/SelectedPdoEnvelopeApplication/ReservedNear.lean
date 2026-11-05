module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.Near
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReserveCompression
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.ReservedMixedJets

/-!
# The exact natural source reserve in the selected PDO annulus

The original parameter Fourier jets produce the actual mixed L² source jets.
Only the finite primitive orders used by the diagonal PDO are compressed;
the output returns to the original scale with natural subtraction, including
its entire low-order plateau. The endpoint and algebraic specializations
supply their primitive symbol profile from the same normalized inverse.
Consumer: `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open ResponseTransfer ResponseTransfer.Complement ResponseTransfer.DirectEvolution
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open CharacteristicTransport.CompleteResidual ResponseTransfer.NearCarrierFullLow
open FixedDomainInverse.FiniteResidualEnvelopes
variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The same selected annular PDO preserves one original source reserve
at every ordered parameter and spatial Sobolev degree. The mixed datum
estimate and stationary source geometry are proved, with no response-output
hypothesis (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_pdo_annular_reserved_ordered_bounds
    (x : E) (radius : ℝ) (hradius : 0 < radius) (χout χsource : E → ℂ)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ ball x radius)
    {ra rb : ℝ} (hra : 0 < ra) (hrb : 0 < rb)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (Aphase Aamp : ℕ → ℝ) (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hAdata : ∀ i, 0 ≤ Adata i)
    (symbol : I → E → E → Mat)
    (hsymbol : ∀ i (adj : Bool),
      let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦ (χout y * χsource z) •
        (annularSelector ra rb hra hrb ((lam i)⁻¹ • ξ) • symbol i y ξ)
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
    (S : Set E) (hS : IsCompact S)
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    let π := annularSelector (n := d+1) ra rb hra hrb
    ∀ adj : Bool,
    let σ := fun i y ξ ↦ π ((lam i)⁻¹ • ξ) • symbol i y ξ
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (σ i)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
          C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
  classical
  intro π adj σ output ps hps s
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
  obtain ⟨C,hC,hbound⟩ := selected_pdo_annular_sobolev_of_finite_scale_compression
    x radius hradius χout χsource hoc hsc hmask hra hrb basis s ps hps hV hKpar hVK
    Rstar (fullLowReserve (d+1)+3) (by omega) Aphase Aamp hAphase hAamp
    lam L Knear Adata hlam hL hKnear hAdata symbol hsymbol
    φ hφ hcap hφjets hphaseScale hampScale S hS a ha has Dprofile hDprofile hcompressed adj
  refine ⟨C,hC,?_⟩
  intro i c hc
  have hb := hbound i c hc
  have he : Knear i ^ (s+ps.length) = K i ^ (s+ps.length-Rsource) :=
    reservedEnvelopeScale_pow_top (hK i) (s+ps.length) Rsource
  simpa only [he] using hb

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
