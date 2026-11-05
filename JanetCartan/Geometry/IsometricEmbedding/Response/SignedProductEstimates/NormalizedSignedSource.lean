module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedTail
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedRestriction

/-!
# Corrected signed-source discrepancy on both quadratures and restrictions

The actual source-tail estimate supplies every analytic bound below. The same
normalized source acts on both complete signed amplitudes and every real
quadrature; literal restriction/zero extension identifies the local error.
All constants precede the original varying sources, histories and domains.
Consumer: `app:ch_pairs:prop:pairs-lag-sum`, Steps 1–3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open ResponseTransfer.SourceNegative Sampling.BackgroundModulation Pseudodifferential
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization LocalSobolev
open RegularSector.Characteristic.RetardedLocalization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp V 2 (volume : Measure E)

/-- Actual corrected-source decay for both full signed amplitudes, with
positive/negative component norms and the original local restriction norm.
The constant and threshold come from the checked source-shell application;
no desired discrepancy bound is an input. Take `c=1` or `c=-I` for the two
quadratures (`pairs-lag-one-error`, `resolved-angular-tail`). -/
theorem exists_normalized_signed_source_quadrature_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K)
    (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    {T : Set E} (hT : IsCompact T) (hTK : T ⊆ K) (hTneg : ∀ v ∈ T, -v ∈ T)
    {S : Set E} (hS : IsCompact S) (hScore : S ⊆ closedBall center f.physicalRadius)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hop : ∀ y ∈ S, output y = 1)
    {a G cbeat : ℝ} (ha : 0 < a) (hG : 0 < G) (hbeat : 0 < cbeat)
    (Cscale : ℝ) (P X Y CQ C : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) (s : ℕ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set E), IsOpen U → S ⊆ U →
      ∀ (χ ψ φ : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1))
        (A B : E → Matrix (Fin N) (Fin (d+1)) ℂ) (R L ρ : ℝ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φ U → ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      tsupport χ ⊆ S → 1 ≤ L → Rmin ≤ R →
      cbeat * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      L ≤ Cscale * R ^ (1+meanSlack) →
      (∀ y ∈ U, a ≤ ‖fderiv ℝ φ y‖ ∧ ‖fderiv ℝ φ y‖ ≤ G) →
      (∀ y ∈ U, NormedSpace.normalize (fderiv ℝ φ y) ∈ (InnerProductSpace.toDual ℝ E) '' T) →
      (∀ y ∈ S, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ (r+1) φ y‖ ≤ P r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ y‖ ≤ X r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ y‖ ≤ Y r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q y‖ ≤ CQ r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A y‖ ≤ C r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B y‖ ≤ C r * L^r) →
      let estimate := fun b : E → V ↦
        let g := modulatedSource χ φ b ρ
        ∃ hg : MemLp g 2 volume, ∀ c : ℂ, ‖c‖ = 1 →
          let u := hg.toLp g
          let e := (realSource f hK L₀ output ho.continuous hob - 1) (l2RealPart volume (c • u))
          (∀ t : ℝ, t ≤ s →
            MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
            componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
              D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
          ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
            let localError := localRealCompression hW Vout
              (pairedSource f hK L₀ output ho.continuous hob - 1)
              (l2RealPart (volume.restrict W) (c • restrictL2 W u))
            MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
              D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹
      estimate (fun y ↦ ψ y • ((1/2 : ℝ) • complexStressContraction (Q y)
        (symmetricBilinearTensor (A y) (B y)))) ∧
      estimate (fun y ↦ ψ y • ((1/2 : ℝ) • complexStressContraction (Q y)
        (symmetricBilinearTensor (A y) ((B y).map conj)))) := by
  obtain ⟨Rmin, hmin, htail⟩ := exists_normalized_signed_source_discrepancy_constants (N := N)
    f hK L₀ hL₀ hT hTK hTneg hS hScore output ho hoc hob hop ha hG hbeat Cscale
    P X Y CQ C hP hX hY hCQ hC s
  obtain ⟨Cr, hCr, hrestriction⟩ := exists_source_quadrature_restriction_comparison (d := d) s
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨D, hD, hsource⟩ := htail q
  refine ⟨max 1 Cr * D, by positivity, ?_⟩
  intro U hU hSU χ ψ φ Q A B R L ρ hχ hψ hQ hφ hA hB hχS hL hR hρ hslow
    hband hprotected hphase hχb hψb hQb hAb hBb
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) (hmin.trans hR)
  obtain ⟨hp, hm⟩ := hsource U hU hSU χ ψ φ Q A B R L ρ hχ hψ hQ hφ hA hB
    hχS hL hR hρ hslow hband hprotected hphase hχb hψb hQb hAb hBb
  have hfull (b : E → V)
      (h : ∃ hg : MemLp (modulatedSource χ φ b ρ) 2 volume, ∀ t : ℝ, t ≤ s →
        let v := (pairedSource f hK L₀ output ho.continuous hob - 1) (hg.toLp (modulatedSource χ φ b ρ))
        MemVectorFourierSobolev t v ∧ vectorFourierSobolevNorm t v ≤
          D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) :
      let g := modulatedSource χ φ b ρ
      ∃ hg : MemLp g 2 volume, ∀ c : ℂ, ‖c‖ = 1 →
        let u := hg.toLp g
        let e := (realSource f hK L₀ output ho.continuous hob - 1) (l2RealPart volume (c • u))
        (∀ t : ℝ, t ≤ s →
          MemComponentFourierSobolev (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ∧
          componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin (d+1)) ℝ) t e ≤
            (max 1 Cr * D) * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) ∧
        ∀ (W : Set E) (hW : MeasurableSet W), tsupport χ ⊆ W → ∀ Vout : Set E,
          let localError := localRealCompression hW Vout
            (pairedSource f hK L₀ output ho.continuous hob - 1)
            (l2RealPart (volume.restrict W) (c • restrictL2 W u))
          MemRestrictionSobolev Vout s localError ∧ restrictionSobolevNorm Vout s localError ≤
            (max 1 Cr * D) * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹ := by
    obtain ⟨hg, hbound⟩ := h
    refine ⟨hg, fun c hc ↦ ⟨?_, ?_⟩⟩
    · intro t ht
      obtain ⟨hm, hn⟩ := normalizedSource_real_quadrature_sobolev_le f hK L₀ output ho.continuous hob
        (hg.toLp _) (hbound t ht).1 c hc
      refine ⟨hm, hn.trans ((hbound t ht).2.trans ?_)⟩
      have hd : D ≤ max 1 Cr * D := le_mul_of_one_le_left hD (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hd (by positivity)
    · intro W hW hχW Vout
      rw [local_normalizedSource_modulated_quadrature_defect f hK L₀ output ho.continuous hob
        χ φ b ρ hg hW hχW Vout c]
      obtain ⟨hm, hn⟩ := hrestriction _ (hbound s le_rfl).1 Vout c hc
      refine ⟨hm, hn.trans ?_⟩
      calc
        _ ≤ Cr * (D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) :=
          mul_le_mul_of_nonneg_left (hbound s le_rfl).2 hCr
        _ ≤ max 1 Cr * (D * ((R ^ carrierExponent * R ^ (-separationExponent))^q)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = _ := by ring
  obtain ⟨hp, hpb⟩ := hp
  obtain ⟨hm, hmb⟩ := hm
  exact ⟨hfull _ ⟨hp, fun t ht ↦ (hpb t ht).1⟩, hfull _ ⟨hm, fun t ht ↦ (hmb t ht).1⟩⟩

end JanetCartan.SignedProductEstimates
