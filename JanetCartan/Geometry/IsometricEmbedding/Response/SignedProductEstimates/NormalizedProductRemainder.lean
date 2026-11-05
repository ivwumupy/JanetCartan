module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedInverseRemainder
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources

/-!
# Inverse remainder on the literal signed product datum

The actual `ProductSum` source is admitted into the SAME normalized inverse's
remainder estimate by exact real-quadrature identities. The complete stress
contraction, both original source cutoffs, full zeroth coefficient and both
inverse masks remain. A plus diagonal needs no difference-phase geometry.
Only the minus diagonal is excluded. Constants and finite depth precede the
samples, source data and finite history.

The remaining operator contraction and forward/literal-adjoint gains are
published by the normalized inverse constructors; the retained initializer and
sampled-amplitude producers still have to supply their same-family inputs.
This is the finite remainder contribution, not complete angular decay on every
residual word. Sources: `app:ch_regular:eq:inverse-remainder`,
`app:ch_pairs:eq:pairs-lag-one-error`. Consumers: `UniformStep.SampledProduct`
and the original finite-Neumann angular observation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius ComplexConjugate
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse ArbitraryAccuracy Pseudodifferential
open ResponseTransfer.SourceNegative Sampling.BackgroundModulation JanetCartan.Localization
open GeometricProfile RegularSector.FiniteEvolution ArbitraryAccuracy.ResidualLocalization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

variable {ι : Type*}

/-- Apply the normalized inverse remainder to the literal reduced plus/minus
source. The signed phase is divided by its own true frequency; no sum or
difference is identified with a single Hamilton primary. The source and all
operators are unchanged as accuracy and derivative order vary
(`app:ch_pairs:prop:pairs-lag-sum`, `app:ch_regular:eq:inverse-remainder`). -/
theorem exists_normalized_product_inverse_remainder_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center)
    {normRadius profileRadius : ℝ} (hnorm : 0 < normRadius) (hbuffer : normRadius < profileRadius)
    {Ssrc Senv : Set E} (hSenv : IsCompact Senv)
    (hSenvU : Senv ⊆ ball center profileRadius) (hSrcW : Ssrc ⊆ ball center normRadius)
    {a b cbeat θ : ℝ} (ha : 0 < a) (hbeat : 0 < cbeat) (hθ : θ < 1)
    (Cscale : ℝ) (P X Y Z AQ AB C Gain : ℕ → ℝ)
    (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r) (hZ : ∀ r, 0 ≤ Z r)
    (hAQ : ∀ r, 0 ≤ AQ r) (hAB : ∀ r, 0 ≤ AB r) (hC : ∀ r, 0 ≤ C r)
    (hGain : ∀ r, 0 ≤ Gain r) {reserve : ℕ}
    (hreserve : sectorLowOrder d + (d+2) ≤ reserve) (s : ℕ) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ depth : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (R Lc Lpair ρ : ℝ), Rmin ≤ R → 1 ≤ Lc → Lc ≤ Lpair →
      Lpair ≤ Cscale * R^(1+meanSlack) →
      cbeat*(R^carrierExponent * R^(-separationExponent)) ≤ ρ →
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B),
      HasDerivativeProfile (closedBall center profileRadius) Q reserve Lc AQ →
      HasDerivativeProfile (closedBall center profileRadius) B reserve Lc AB →
      let W := ball center normRadius
      let uQ := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) Q hQ.contDiffOn
      let uB := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) B hB.contDiffOn
      let coeff := fun k ↦ restrictionSobolevNorm W k uQ + restrictionSobolevNorm W k uB
      let β := sectorLowOrder d + (d+2)
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H),
      let Krecut := localRealCompression (U := W) isOpen_ball.measurableSet W
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (SmallSupport.bump_norm_le_one χ₂) (SmallSupport.bump_norm_le_one χ₃)
          (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
      ‖Krecut‖ ≤ θ →
      (∀ (k : ℕ) (v : LocalL2 W E), MemRestrictionSobolev W k v →
        (MemRestrictionSobolev W (k+1) (Krecut v) ∧
          restrictionSobolevNorm W (k+1) (Krecut v) ≤ Gain (k+1) *
            (restrictionSobolevNorm W k v + (1+coeff (k+1+β))*‖v‖)) ∧
        (MemRestrictionSobolev W (k+1) (Krecut.adjoint v) ∧
          restrictionSobolevNorm W (k+1) (Krecut.adjoint v) ≤ Gain (k+1) *
            (restrictionSobolevNorm W k v + (1+coeff (k+1+β))*‖v‖))) →
      ∀ (χ ψ η : E → ℝ) (phases : ι → E → ℝ)
        (amplitudes : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
        (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let φ := fun y ↦ (if minus then phases i y - phases j y else phases i y + phases j y) / ρ
      SourceGeometry χ φ Ssrc a b Lpair P X →
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Senv → EqOn ψ (fun _ ↦ 1) (tsupport χ) →
      ContDiffOn ℝ ∞ η (ball center profileRadius) →
      ContDiffOn ℝ ∞ (amplitudes i) (ball center profileRadius) →
      ContDiffOn ℝ ∞ (amplitudes j) (ball center profileRadius) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k ψ y‖ ≤ Y k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k η y‖ ≤ Z k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes i) y‖ ≤ C k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes j) y‖ ≤ C k * Lpair^k) →
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun z ↦ χ z •
          (if minus then ProductSum.minusSource phases amplitudes i j z
            else ProductSum.plusSource phases amplitudes i j z))) y)
      ∃ hg : MemLp g 2 volume,
        let h := (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g
        MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ∧
        restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ≤
          D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ := by
  obtain ⟨Rmin, hmin, hconstants⟩ := exists_normalized_signed_inverse_remainder_constants
    (N := N) (b := b) f hK L₀ output ho hob χ₂ χ₃ hnorm hbuffer hSenv hSenvU hSrcW
    ha hbeat hθ Cscale P X Y Z AQ AB C Gain hX hY hZ hAQ hAB hC hGain hreserve s
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨depth, D, hD, hbound⟩ := hconstants q
  refine ⟨depth, D, hD, ?_⟩
  intro R Lc Lpair ρ hR hLc hLcPair hslow hρ Q B hQ hB hpQ hpB
    W uQ uB coeff β W₁ retarded Krecut hKrecut hgain χ ψ η phases amplitudes
    minus i j _hdiag φ gφ hψ hψS hone hη hA hAp hψb hηb hAb hApb g
  have hRp : 0 < R := (by norm_num : (0 : ℝ) < 2).trans_le (hmin.trans hR)
  have hρpos : 0 < ρ := (mul_pos hbeat (by positivity)).trans_le hρ
  obtain ⟨hp, hm, hpm⟩ := hbound R Lc Lpair ρ ρ hR hLc hLcPair hslow hρ hρ
    Q B hQ hB hpQ hpB W₁ retarded hKrecut hgain χ ψ η φ φ gφ gφ hψ hψS hone
    (amplitudes i) (amplitudes j) hη hA hAp hψb hηb hAb hApb
  have hfinish (v : E → V)
      (hv : MemLp (modulatedSource χ φ v ρ) 2 volume)
      (he : g = fun y ↦ euclideanRealPart (modulatedSource χ φ v ρ y))
      (hb :
        let h := l2RealPart (volume.restrict W)
          (restrictL2 W (hv.toLp (modulatedSource χ φ v ρ)));
        MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ∧
        restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ≤
          D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) :
      ∃ hg : MemLp g 2 volume,
        let h := (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g
        MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ∧
        restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ≤
          D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ := by
    let z := hv.toLp (modulatedSource χ φ v ρ)
    have hrep : l2RealPart volume z =ᵐ[volume] g := by
      rw [he]
      filter_upwards [euclideanRealPart.coeFn_compLpL z, hv.coeFn_toLp] with y hr hz
      exact hr.trans (congrArg euclideanRealPart hz)
    have hg : MemLp g 2 volume := (Lp.memLp (l2RealPart volume z)).ae_eq hrep
    have heq : (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g =
        l2RealPart (volume.restrict W) (restrictL2 W z) := by
      apply Lp.ext
      filter_upwards [(hg.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
        euclideanRealPart.coeFn_compLpL (restrictL2 W z), restrictL2_coeFn W z,
        ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL z), ae_restrict_of_ae hrep]
          with y hg' hr hl hgr hgR
      change (l2RealPart (volume.restrict W) (restrictL2 W z)) y = _ at hr
      change (l2RealPart volume z) y = _ at hgr
      rw [hg', hr, hl, ← hgr, hgR]
    refine ⟨hg, ?_⟩
    dsimp only
    rw [heq]
    exact hb
  cases minus with
  | false =>
    exact hfinish _ hp
      (cutoff_stressSource_plus_eq_real_modulatedSource Q χ η phases amplitudes i j hρpos.ne')
      (by simpa only [one_smul] using (hpm 1 (by simp)).1)
  | true =>
    exact hfinish _ hm
      (cutoff_stressSource_minus_eq_real_modulatedSource Q χ η phases amplitudes i j hρpos.ne')
      (by simpa only [one_smul] using (hpm 1 (by simp)).2)

end JanetCartan.SignedProductEstimates
