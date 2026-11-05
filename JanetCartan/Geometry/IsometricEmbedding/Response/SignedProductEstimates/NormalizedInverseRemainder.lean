module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedNegativeSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ScaleGap
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureSource
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.CoefficientProfiles
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Measured
public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Estimates

/-!
# Original signed-source remainder for the normalized complete inverse

Apply the existing negative Fourier bound to the full signed stress sources,
and derive the inverse coefficient profile from the original principal and
complete zeroth coefficient jets. The one inverse is the literal real
compression of the normalized residual, recut by the same two physical masks.
The original scale gap selects a finite depth before the varying sources.
Both real quadratures have arbitrary decay at the unchanged separated stage
frequency. The angular observation on all finite residual words is separate.

The contraction and forward/literal-adjoint gain inputs are the outputs of
`FixedDomainInverse.exists_normalized_complete_fixed_inverse_of_selected_collar`
and `exists_pre_reference_terminal_normalized_history_inverse`. The precise
operator identification is `NormalizedResidualWords.localizedResidual_normalized_eq_measured`.
The retained history coefficient and signed-family geometry producers supply
the profiles used here. Their application on one initialized family remains
with the actual response construction; no independent choices are equated.

Consumers: `ArbitraryAccuracy.rapidDecayAt_inverse_of_finite_chains` and
`UniformStep.SampledProduct`. Sources: `app:ch_regular:eq:inverse-remainder`,
`app:ch_pairs:prop:pairs-lag-sum`, `main:eq:all-pair-scales`.
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

/-- The original signed sources have an arbitrarily small remainder under
one fixed normalized complete inverse. Only its published contraction and
forward/literal-adjoint one-gain outputs are required; all negative-source
and coefficient-profile inputs are proved from the primitive source and
coefficient jets. The depth and constant precede coefficients and sources
(`app:ch_regular:eq:inverse-remainder`, `app:ch_pairs:prop:pairs-lag-sum`). -/
theorem exists_normalized_signed_inverse_remainder_constants
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
      ∀ (R Lc Lpair ρp ρm : ℝ), Rmin ≤ R → 1 ≤ Lc → Lc ≤ Lpair →
      Lpair ≤ Cscale * R^(1+meanSlack) →
      cbeat*(R^carrierExponent * R^(-separationExponent)) ≤ ρp →
      cbeat*(R^carrierExponent * R^(-separationExponent)) ≤ ρm →
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
      ∀ (χ ψ η φp φm : E → ℝ),
      SourceGeometry χ φp Ssrc a b Lpair P X → SourceGeometry χ φm Ssrc a b Lpair P X →
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Senv → EqOn ψ (fun _ ↦ 1) (tsupport χ) →
      ∀ (A Ap : E → Matrix (Fin N) (Fin (d+1)) ℂ),
      ContDiffOn ℝ ∞ η (ball center profileRadius) →
      ContDiffOn ℝ ∞ A (ball center profileRadius) →
      ContDiffOn ℝ ∞ Ap (ball center profileRadius) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k ψ y‖ ≤ Y k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k η y‖ ≤ Z k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k A y‖ ≤ C k * Lpair^k) →
      (∀ y ∈ ball center profileRadius, ∀ k, ‖iteratedFDeriv ℝ k Ap y‖ ≤ C k * Lpair^k) →
      let p := modulatedSource χ φp (fun y ↦ η y • ((1/2 : ℝ) •
        complexStressContraction (Q y) (symmetricBilinearTensor (A y) (Ap y)))) ρp
      let m := modulatedSource χ φm (fun y ↦ η y • ((1/2 : ℝ) •
        complexStressContraction (Q y) (symmetricBilinearTensor (A y) ((Ap y).map conj)))) ρm
      ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume, ∀ ζ : ℂ, ‖ζ‖ = 1 →
        let up := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hp.toLp p))
        let um := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp m))
        (MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) up)) ∧
          restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) up)) ≤
            D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) ∧
        (MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) um)) ∧
          restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) um)) ≤
            D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹) := by
  obtain ⟨Rmin, hmin, hscale⟩ := exists_signed_pair_scale_threshold hbeat Cscale
  have coefficientData := exists_coefficient_pair_inverse_profile (n := d+1) center hnorm hbuffer
    AQ AB hAQ hAB (sectorLowOrder d + (d+2)) reserve hreserve
  rcases coefficientData with ⟨Dcoeff, hDcoeff, hcoeff⟩
  obtain ⟨Dsource, hDsource, hnegative⟩ := exists_reduced_signed_negative_source_constants (n := d+1) (N := N) (G := b)
    hSenv Ssrc ha (by norm_num : (0 : ℝ) < 1/1000) (by norm_num : (1/1000 : ℝ) < 1)
    P X Y Z AQ C hX hY hZ hAQ hC
  refine ⟨Rmin,hmin,fun q ↦ ?_⟩
  obtain ⟨depth, _, hdepth⟩ := exists_tail_order (by norm_num : (0 : ℝ) < 1/1000) s q
  let cost := inverseTameConstant θ Gain s * (powerGainConstant Gain Dcoeff s + Dcoeff s) *
    ((localDualityConstant (d+1) depth (EuclideanSpace.basisFun (Fin (d+1)) ℝ) * Dsource depth) *
      powerGainConstant Gain Dcoeff depth)
  have hcost : 0 ≤ cost := mul_nonneg
    (mul_nonneg (inverseTameConstant_pos hθ hGain s).le
      (add_nonneg (powerGainConstant_nonneg hGain (fun k ↦ (hDcoeff k).le) _) (hDcoeff s).le))
    (mul_nonneg (mul_nonneg (localDualityConstant_pos _ _ _).le (hDsource _))
      (powerGainConstant_nonneg hGain (fun k ↦ (hDcoeff k).le) _))
  refine ⟨depth, cost * (cbeat^q)⁻¹, mul_nonneg hcost (inv_nonneg.mpr (pow_nonneg hbeat.le _)), ?_⟩
  intro R Lc Lpair ρp ρm hR hLc hLcPair hslow hρp hρm Q B hQ hB hpQ hpB
    W uQ uB coeff β W₁ retarded Krecut hKrecut hgain χ ψ η φp φm gp gm hψ hψS hone
    A Ap hη hA hAp hψb hηb hAb hApb p m
  have hLpair : 1 ≤ Lpair := hLc.trans hLcPair
  obtain ⟨hp2,hpgap⟩ := hscale R hR ρp Lpair hρp hslow
  obtain ⟨hm2,hmgap⟩ := hscale R hR ρm Lpair hρm hslow
  have hQjets y (hy : y ∈ ball center profileRadius) k :
      ‖iteratedFDeriv ℝ k Q y‖ ≤ AQ k * Lpair^k := by
    apply (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) (hQ.of_le (by simp))
      (ball_subset_closedBall hy) le_rfl).trans ((hpQ k).trans ?_)
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (zero_le_one.trans hLc) hLcPair _).trans
        (pow_le_pow_right₀ hLpair (Nat.sub_le _ _))) (hAQ k)
  obtain ⟨hp,hm,hn⟩ := hnegative (ball center profileRadius) isOpen_ball χ ψ η φp φm Lpair ρp ρm
    gp gm hψ hψS (hψS.trans hSenvU) hone (by linarith) (by linarith) hpgap hmgap
    Q A Ap hη hQ.contDiffOn hA hAp hψb hηb hQjets hAb hApb
  have hprofile k : 1+coeff (k+β) ≤ Dcoeff k * Lpair^k := by
    have hc := hcoeff isOpen_univ (subset_univ _) Q B hQ hB Lc hLc hpQ hpB k
    have hc' : 1+coeff (k+β) ≤ Dcoeff k * Lc^k := by
      simpa only [coeff,uQ,uB,β,add_assoc] using hc
    apply hc'.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hLc) hLcPair _) (hDcoeff k).le
  have hcoeffpos k : 0 ≤ coeff k := add_nonneg restrictionSobolevNorm_nonneg restrictionSobolevNorm_nonneg
  have hcoeffmono : Monotone coeff := fun k l hkl ↦ add_le_add
    (restrictionSobolevNorm_mono
      (smoothCoefficientL2_memRestrictionSobolev isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) Q hQ.contDiffOn l) hkl)
    (restrictionSobolevNorm_mono
      (smoothCoefficientL2_memRestrictionSobolev isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) B hB.contDiffOn l) hkl)
  refine ⟨hp,hm,fun ζ hζ ↦ ?_⟩
  have hbound (φ : E → ℝ) (v : E → V) (ρ : ℝ)
      (hρtwo : 2 ≤ ρ) (hgap : Lpair ≤ ρ^(1-1/1000 : ℝ))
      (hρ : cbeat*(R^carrierExponent*R^(-separationExponent)) ≤ ρ)
      (hv : MemLp (modulatedSource χ φ v ρ) 2 volume)
      (hn : vectorFourierSobolevNorm (-(depth : ℝ)) (hv.toLp (modulatedSource χ φ v ρ)) ≤
        Dsource depth * (ρ^depth)⁻¹) :
      let u := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hv.toLp (modulatedSource χ φ v ρ)))
      MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) u)) ∧
      restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) u)) ≤
        (cost*(cbeat^q)⁻¹)*((R^carrierExponent*R^(-separationExponent))^q)⁻¹ := by
    intro u
    have hsource := (modulatedSource_real_quadrature_negative_norm_le isOpen_ball.measurableSet
      χ φ v ρ (gp.support_subset.trans hSrcW) hv depth ζ hζ).trans hn
    obtain ⟨hmem,hremainder⟩ := inverse_remainder_restrictionSobolev
      (EuclideanSpace.basisFun (Fin (d+1)) ℝ) isOpen_ball.measurableSet Krecut
      hKrecut hθ hLpair (by linarith : 0 < ρ) (by norm_num : (0 : ℝ) ≤ 1) (hDsource depth)
      hGain hGain (fun k ↦ (hDcoeff k).le) hcoeffpos hcoeffmono hprofile
      (fun k v hv ↦ (hgain k v hv).1.1) (fun k v hv ↦ (hgain k v hv).1.2)
      (fun k v hv ↦ (hgain k v hv).2.1) (fun k v hv ↦ (hgain k v hv).2.2)
      depth s u (by simpa only [mul_one, div_eq_mul_inv] using hsource)
    have hLpρ : Lpair ≤ ρ := hgap.trans (Real.rpow_le_self_of_one_le (by linarith)
      (by norm_num : (1-1/1000 : ℝ) ≤ 1))
    have hdecay : Lpair^s * (Lpair/ρ)^depth ≤ (ρ^q)⁻¹ := by
      apply (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans hLpair) hLpρ s) (by positivity)).trans
      simpa only [Real.rpow_natCast, Real.rpow_neg (by linarith : 0 ≤ ρ)] using
        tail_factor_le_negative_power (by linarith : 1 ≤ ρ) (zero_le_one.trans hLpair) hgap hdepth
    have hRp : 0 < R := (by norm_num : (0 : ℝ) < 2).trans_le (hmin.trans hR)
    have hstage : (ρ^q)⁻¹ ≤ (cbeat^q)⁻¹*((R^carrierExponent*R^(-separationExponent))^q)⁻¹ := by
      simpa only [mul_pow,mul_inv_rev,mul_comm] using
        ProductSum.inverse_pow_le_of_scale_le (by positivity) hρ q
    refine ⟨hmem, hremainder.trans ?_⟩
    calc
      _ = cost * (Lpair^s*(Lpair/ρ)^depth) := by dsimp only [cost]; ring
      _ ≤ cost*((cbeat^q)⁻¹*((R^carrierExponent*R^(-separationExponent))^q)⁻¹) :=
        mul_le_mul_of_nonneg_left (hdecay.trans hstage) hcost
      _ = _ := by ring
  exact ⟨hbound φp _ ρp hp2 hpgap hρp hp (hn depth).1.2,
    hbound φm _ ρm hm2 hmgap hρm hm (hn depth).2.2⟩

end JanetCartan.SignedProductEstimates
