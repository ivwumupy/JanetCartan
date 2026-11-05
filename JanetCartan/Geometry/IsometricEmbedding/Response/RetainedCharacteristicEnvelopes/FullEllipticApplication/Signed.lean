module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.Complete
public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.Reserved
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.Conjugation

/-!
# Whole conjugates of the complete elliptic envelopes

Whole-operator conjugation reverses the source carrier. The negative source
phase and the conjugated original datum satisfy the same primitive profiles;
applying the actual complete elliptic estimate to them therefore proves the
reflected letters, as well as their literal adjoints.

Consumer: the external half-pair in the SAME normalized solver and residual,
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
open RegularSector.Realization CharacteristicTransport.CompleteResidual
open FixedDomainInverse.FiniteResidualEnvelopes

variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

local instance : StarModule ℝ H where
  star_smul c u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • u),Lp.coeFn_smul c u,
      Lp.coeFn_smul (star c) (star u),Lp.coeFn_star u] with x h₁ h₂ h₃ h₄
    simp only [Pi.star_apply] at h₁ h₄
    simp only [h₃,Pi.smul_apply,h₄,star_smul]

private theorem original_source_star_parameterJet
    (a : E × Par → F) (l : ℕ) (w : Fin l → Par) (c : Par) (y : E) :
    iteratedFDeriv ℝ l (fun q ↦ star (a (y,q))) c w =
      star (iteratedFDeriv ℝ l (fun q ↦ a (y,q)) c w) :=
  congrArg (fun D : Par [×l]→L[ℝ] F ↦ D w)
    ((starL' ℝ : F ≃L[ℝ] F).iteratedFDeriv_comp_left)

private theorem original_source_star_fourier_profiles
    (a : I → E × Par → F) (A K : I → ℝ) (V : Set Par) (C : ℕ → ℕ → ℝ) (power : ℕ → ℕ → ℕ)
    (hsource : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C l s * A i * K i ^ (power s l)) :
    ∃ Cstar : ℕ → ℕ → ℝ,
      ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ star (a i (y,q))) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Cstar l s * A i * K i ^ (power s l) := by
  choose D hD hstar using exists_star_fourierSobolev_constant (d+1) (d+1)
  refine ⟨fun l s ↦ D s * C l s,?_⟩
  intro i c hc l w hw s fstar
  obtain ⟨hm,hmem,hbound⟩ := hsource i c hc l w hw s
  let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
  have heq : fstar = star f := funext fun y ↦ original_source_star_parameterJet (a i) l w c y
  rw [heq]
  have hLp : hm.star.toLp (star f) = star (hm.toLp f) := by
    apply Lp.ext
    filter_upwards [hm.star.coeFn_toLp,Lp.coeFn_star (hm.toLp f),hm.coeFn_toLp] with y hy hs hf
    have hf' : (hm.toLp f) y = f y := hf
    have hs' : (star (hm.toLp f)) y = star ((hm.toLp f) y) := hs
    exact hy.trans ((congrArg star hf').symm.trans hs'.symm)
  obtain ⟨hstarMem,hstarBound⟩ := hstar s (hm.toLp f) hmem
  rw [← hLp] at hstarMem hstarBound
  exact ⟨hm.star,hstarMem,
    hstarBound.trans
      ((mul_le_mul_of_nonneg_left hbound (hD s).le).trans_eq (by ring))⟩

private theorem carrierMultiplication_neg_source_phase (ρ : ℝ) (φ : E → ℝ)
    (hφ : Continuous φ) :
    carrierMultiplication (r := d+1) ρ (fun y ↦ -φ y) hφ.neg =
      carrierMultiplication (-ρ) φ hφ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [carrierMultiplication_ae ρ (fun y ↦ -φ y) hφ.neg u,
    carrierMultiplication_ae (-ρ) φ hφ u] with y hy hz
  rw [hy,hz]
  simp only [carrier,mul_neg,neg_mul]

variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

/-- The actual full elliptic inverse and residual, their literal adjoints,
and their whole conjugates satisfy the same ordered source estimates. The
reflected case is proved by applying the complete estimate to the opposite
source phase and the conjugated actual datum; every source hypothesis is
derived from the original one (`app:ch_response:eq:response-graded-reduced`). -/
theorem complete_elliptic_signed_ordered_envelopes
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    (threshold : ℝ) (ht : fam.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rstar : ℕ) (hRstar : fullLowReserve (d+1)+2 < Rstar)
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
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l)) :
    ∀ residual adj reflected : Bool,
    let σ := fun i y ξ ↦
      if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
        else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ
    let T := fun i ↦ annularGraphOrientation adj
      (maskedPhysicalPDO χout (fun y ↦ (fam.inputMask y : ℂ)) (σ i))
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (if reflected then boundedConjugate (T i) else T i)
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    (∀ i, ContDiffOn ℝ ∞ (output i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output q.1) q.2)
        (fun q ↦ lam q.1 ^ (-1 : ℤ) * Adata q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  classical
  intro residual adj reflected σ T output
  cases reflected
  · exact complete_elliptic_ordered_envelopes fam hK₀ hΩcoeff hball χout ho hoc hos threshold ht
      basis hV hKpar hVK Rstar hRstar AQ AB Aphase hAQ hAB hAphase hν hν1 ha₀ hB₀
      lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQl hBl hQp hBp
      φ hφ hcap hφjets hsourceBand S hS hSU a ha has Csource hfourier residual adj
  · let φneg := fun i y c ↦ -φ i y c
    have hφneg i : ContDiff ℝ ∞ (Function.uncurry (φneg i)) := (hφ i).neg
    have hcapneg i : cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
        (Function.uncurry (φneg i)) ≤ Aphase 2 := by
      change cNorm _ _ (-Function.uncurry (φ i)) ≤ _
      simpa only [cNorm_neg] using hcap i
    have hφnegjets i j q (hq : q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar) :
        ‖iteratedFDeriv ℝ j (Function.uncurry (φneg i)) q‖ ≤ Aphase j * L i ^ (j-Rstar) := by
      change ‖iteratedFDeriv ℝ j (-Function.uncurry (φ i)) q‖ ≤ _
      simpa only [iteratedFDeriv_neg_apply,norm_neg] using hφjets i j q hq
    have hnegativeBand i c (hc : c ∈ V) y (hy : y ∈ ball x (3*fam.physicalRadius)) :
        a₀ ≤ ‖fderiv ℝ (fun z ↦ φneg i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φneg i z c) y‖ ≤ B₀ := by
      change a₀ ≤ ‖fderiv ℝ (-(fun z ↦ φ i z c)) y‖ ∧
        ‖fderiv ℝ (-(fun z ↦ φ i z c)) y‖ ≤ B₀
      simpa only [fderiv_neg,norm_neg] using hsourceBand i c hc y hy
    let astar := fun i q ↦ star (a i q)
    have hastar i : ContDiff ℝ ∞ (astar i) := (starL' ℝ : F ≃L[ℝ] F).contDiff.comp (ha i)
    have hsastar i q (hq : q.1 ∉ S) : astar i q = 0 := by simp only [astar,has i q hq,star_zero]
    obtain ⟨Cstar,hstar⟩ := original_source_star_fourier_profiles a Adata K V Csource (fun s l ↦ s+l) hfourier
    have hnegative := complete_elliptic_ordered_envelopes fam hK₀ hΩcoeff hball χout ho hoc hos threshold ht
      basis hV hKpar hVK Rstar hRstar AQ AB Aphase hAQ hAB hAphase hν hν1 ha₀ hB₀
      lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQl hBl hQp hBp
      φneg hφneg hcapneg hφnegjets hnegativeBand S hS hSU astar hastar hsastar Cstar hstar residual adj
    let negative := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φneg i y c)
      ((hφneg i).continuous.comp (continuous_id.prodMk continuous_const)) (T i)
      (graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c))
    have hnegativeSm : ∀ i, ContDiffOn ℝ ∞ (negative i) V := hnegative.1
    have hdatumStar i c : graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c) =
        star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) := by
      apply Lp.ext
      filter_upwards [vectorOriginalDatumTest_toLp_ae (astar i) (hastar i) hS (hsastar i) [] c,
        Lp.coeFn_star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)),
        vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c] with y hb hs hadatum
      change (star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) y =
        star ((graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) y) at hs
      rw [hadatum] at hs
      exact hb.trans hs.symm
    have heq i : output i = fun c ↦ star (negative i c) := by
      funext c
      change carrierMultiplication (-(lam i)) (fun y ↦ φ i y c) _
        (boundedConjugate (T i) (carrierMultiplication (lam i) (fun y ↦ φ i y c) _
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))) = _
      rw [demodulated_boundedConjugate_eq]
      congr 1
      simp only [negative,demodulatedL2Operator,ContinuousLinearMap.comp_apply,φneg,hdatumStar]
      have hpc : Continuous (fun y ↦ φ i y c) :=
        (hφ i).continuous.comp (continuous_id.prodMk continuous_const)
      rw [carrierMultiplication_neg_source_phase (-(lam i)) (fun y ↦ φ i y c) hpc,
        carrierMultiplication_neg_source_phase (lam i) (fun y ↦ φ i y c) hpc,neg_neg]
    refine ⟨fun i ↦ ((starL' ℝ : H ≃L[ℝ] H).contDiff.comp_contDiffOn (hnegativeSm i)).congr
      (fun c _ ↦ congrFun (heq i) c),?_⟩
    intro ps hps
    have hh := hasEnvelopeProfile_star (hnegative.2 ps hps)
    apply (hasEnvelopeProfile_congr (f := fun q : I × V ↦
      star (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (negative q.1) q.2)) ?_).mp hh
    intro q
    rw [heq,orderedTransferAction_star]


/-- The whole conjugates of the same complete elliptic operators retain the
exact natural source reserve. Negating the original phase and conjugating the
actual datum preserve their primitive profiles; the finite near calculus
spends only `fullLowReserve + 3` of the original coefficient reserve
(`app:ch_response:eq:response-graded-reduced`). -/
theorem complete_elliptic_signed_reserved_ordered_bounds
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
    ∀ residual adj reflected : Bool,
    let σ := fun i y ξ ↦
      if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
        else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ
    let T := fun i ↦ annularGraphOrientation adj
      (maskedPhysicalPDO χout (fun y ↦ (fam.inputMask y : ℂ)) (σ i))
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (if reflected then boundedConjugate (T i) else T i)
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
  intro residual adj reflected σ T output
  cases reflected
  · exact complete_elliptic_reserved_ordered_bounds fam hK₀ hΩcoeff hball χout ho hoc hos threshold ht
      basis hV hKpar hVK Rsource Rstar hRstar AQ AB Aphase hAQ hAB hAphase hν hν1 ha₀ hB₀
      lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQl hBl hQp hBp
      φ hφ hcap hφjets hsourceBand S hS hSU a ha has Csource hfourier residual adj
  · let φneg := fun i y c ↦ -φ i y c
    have hφneg i : ContDiff ℝ ∞ (Function.uncurry (φneg i)) := (hφ i).neg
    have hcapneg i : cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
        (Function.uncurry (φneg i)) ≤ Aphase 2 := by
      change cNorm _ _ (-Function.uncurry (φ i)) ≤ _
      simpa only [cNorm_neg] using hcap i
    have hφnegjets i j q (hq : q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar) :
        ‖iteratedFDeriv ℝ j (Function.uncurry (φneg i)) q‖ ≤ Aphase j * L i ^ (j-Rstar) := by
      change ‖iteratedFDeriv ℝ j (-Function.uncurry (φ i)) q‖ ≤ _
      simpa only [iteratedFDeriv_neg_apply,norm_neg] using hφjets i j q hq
    have hnegativeBand i c (hc : c ∈ V) y (hy : y ∈ ball x (3*fam.physicalRadius)) :
        a₀ ≤ ‖fderiv ℝ (fun z ↦ φneg i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φneg i z c) y‖ ≤ B₀ := by
      change a₀ ≤ ‖fderiv ℝ (-(fun z ↦ φ i z c)) y‖ ∧
        ‖fderiv ℝ (-(fun z ↦ φ i z c)) y‖ ≤ B₀
      simpa only [fderiv_neg,norm_neg] using hsourceBand i c hc y hy
    let astar := fun i q ↦ star (a i q)
    have hastar i : ContDiff ℝ ∞ (astar i) := (starL' ℝ : F ≃L[ℝ] F).contDiff.comp (ha i)
    have hsastar i q (hq : q.1 ∉ S) : astar i q = 0 := by simp only [astar,has i q hq,star_zero]
    obtain ⟨Cstar,hstar⟩ := original_source_star_fourier_profiles a Adata K V Csource (fun s l ↦ s+l-Rsource) hfourier
    have hnegative := complete_elliptic_reserved_ordered_bounds fam hK₀ hΩcoeff hball χout ho hoc hos threshold ht
      basis hV hKpar hVK Rsource Rstar hRstar AQ AB Aphase hAQ hAB hAphase hν hν1 ha₀ hB₀
      lam L K Adata hlam hL hLK hscale hAdata Q B hQ hB hmap hQl hBl hQp hBp
      φneg hφneg hcapneg hφnegjets hnegativeBand S hS hSU astar hastar hsastar Cstar hstar residual adj
    let negative := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φneg i y c)
      ((hφneg i).continuous.comp (continuous_id.prodMk continuous_const)) (T i)
      (graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c))
    have hnegativeSm : ∀ i, ContDiffOn ℝ ∞ (negative i) V := hnegative.1
    have hdatumStar i c : graphTestToLp (vectorOriginalDatumTest (astar i) (hastar i) hS (hsastar i) [] c) =
        star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) := by
      apply Lp.ext
      filter_upwards [vectorOriginalDatumTest_toLp_ae (astar i) (hastar i) hS (hsastar i) [] c,
        Lp.coeFn_star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)),
        vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c] with y hb hs hadatum
      change (star (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) y =
        star ((graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)) y) at hs
      rw [hadatum] at hs
      exact hb.trans hs.symm
    have heq i : output i = fun c ↦ star (negative i c) := by
      funext c
      change carrierMultiplication (-(lam i)) (fun y ↦ φ i y c) _
        (boundedConjugate (T i) (carrierMultiplication (lam i) (fun y ↦ φ i y c) _
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))) = _
      rw [demodulated_boundedConjugate_eq]
      congr 1
      simp only [negative,demodulatedL2Operator,ContinuousLinearMap.comp_apply,φneg,hdatumStar]
      have hpc : Continuous (fun y ↦ φ i y c) :=
        (hφ i).continuous.comp (continuous_id.prodMk continuous_const)
      rw [carrierMultiplication_neg_source_phase (-(lam i)) (fun y ↦ φ i y c) hpc,
        carrierMultiplication_neg_source_phase (lam i) (fun y ↦ φ i y c) hpc,neg_neg]
    refine ⟨fun i ↦ ((starL' ℝ : H ≃L[ℝ] H).contDiff.comp_contDiffOn (hnegativeSm i)).congr
      (fun c _ ↦ congrFun (heq i) c),?_⟩
    intro ps hps s
    obtain ⟨C,hC,hbound⟩ := hnegative.2 ps hps s
    obtain ⟨D,hD,hstarBound⟩ := exists_star_fourierSobolev_constant (d+1) (d+1) s
    refine ⟨D*C,mul_nonneg hD.le hC,?_⟩
    intro i c hc
    obtain ⟨hm,hb⟩ := hbound i c hc
    rw [heq,orderedTransferAction_star]
    obtain ⟨hsm,hsb⟩ := hstarBound _ hm
    exact ⟨hsm,hsb.trans ((mul_le_mul_of_nonneg_left hb hD.le).trans_eq (by ring))⟩

end JanetCartan.ResponseTransfer.FullEllipticApplication
