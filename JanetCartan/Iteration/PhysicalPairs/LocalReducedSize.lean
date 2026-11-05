module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedRestriction
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.CoefficientProfiles
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.Measured

/-!
# Localized full-source profiles for the SAME normalized inverse

Only the source cutoff buffer carries phase and amplitude jets. The full Q/B
coefficient profiles still live on the inverse norm/profile ball, which may be
arbitrarily larger. The existing supported-source Fourier producer proves global
source Sobolev profiles from these LOCAL jets. No amplitude or phase is replaced,
and the actual source, restricted datum, Corr and solver are unchanged. Consumer:
`main:prop:pairs`, localized original physical size.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius ComplexConjugate
namespace JanetCartan.PhysicalPairs
open SignedProductEstimates
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse Pseudodifferential
open ResponseTransfer.SourceNegative Sampling.BackgroundModulation JanetCartan.Localization
open GeometricProfile RegularSector.FiniteEvolution ArbitraryAccuracy.ResidualLocalization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
variable {ι : Type*}

/-- The literal reduced plus/minus response of the same corrected normalized
solver has carrier-scale size at every natural Sobolev order
(`app:ch_pairs:eq:pairs-lag-sum-size`). Both original source cutoffs, the full
tensor amplitudes and full zeroth coefficient remain. The plus diagonal is
included. Constants precede the frequencies, samples and varying coefficients;
no accuracy parameter enters. The only operator estimate used is the raw
strong tame output of the named normalized inverse constructors. -/
theorem exists_localized_normalized_product_reduced_solver_size_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center)
    {normRadius profileRadius : ℝ} (hnorm : 0 < normRadius) (hbuffer : normRadius < profileRadius)
    {S : Set E} (hS : IsCompact S)
    (P X Y AQ AB C responseCost : ℕ → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hAQ : ∀ r, 0 ≤ AQ r) (hAB : ∀ r, 0 ≤ AB r) (hC : ∀ r, 0 ≤ C r)
    (hresponseCost : ∀ r, 0 ≤ responseCost r) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    {reserve : ℕ} (hreserve : sectorLowOrder d + (d+2) ≤ reserve) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (Lc Lpair lam ρ : ℝ), 1 ≤ Lc → Lc ≤ Lpair → Lpair ≤ lam →
      0 < ρ → ρ ≤ Cfreq * lam →
      ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1))
        (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B),
      HasDerivativeProfile (closedBall center profileRadius) Q reserve Lc AQ →
      HasDerivativeProfile (closedBall center profileRadius) B reserve Lc AB →
      let W := ball center normRadius
      let uQ := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) Q hQ.contDiffOn
      let uB := smoothCoefficientL2 isOpen_univ hnorm (show closedBall center normRadius ⊆ Set.univ from subset_univ _) B hB.contDiffOn
      let coeff := fun k ↦ restrictionSobolevNorm W k uQ + restrictionSobolevNorm W k uB
      let β := sectorLowOrder d + (d+2)
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : ℕ → H →L[ℂ] H),
      let Krecut := localRealCompression (U := W) isOpen_ball.measurableSet W
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (SmallSupport.bump_norm_le_one χ₂) (SmallSupport.bump_norm_le_one χ₃)
          (pairedResidual f hK L₀ Q B output ho hob W₁ (retarded 1)))
      let Corr := fun u : LocalL2 W E ↦ neumannInverse Krecut
        (SmallSupport.bumpL2 (p := 2) le_rfl χ₂ u)
      (∀ (r : ℕ) (u : LocalL2 W E), MemRestrictionSobolev W r u → ∀ Vout : Set E,
        let Su := localRealCompression isOpen_ball.measurableSet Vout
          (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr u)
        MemRestrictionSobolev Vout r Su ∧ restrictionSobolevNorm Vout r Su ≤ responseCost r *
          (restrictionSobolevNorm W r u + (1+coeff (r+β))*‖u‖)) →
      ∀ (Usource : Set E), IsOpen Usource → Usource ⊆ ball center profileRadius →
      ∀ (χ η : E → ℝ) (phases : ι → E → ℝ)
        (amplitudes : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
        (minus : Bool) (i j : ι), (minus = true → i ≠ j) →
      let φ := fun y ↦ (if minus then phases i y - phases j y else phases i y + phases j y) / ρ
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ Usource →
      ContDiffOn ℝ ∞ η (Usource) →
      ContDiffOn ℝ ∞ φ (Usource) →
      ContDiffOn ℝ ∞ (amplitudes i) (Usource) →
      ContDiffOn ℝ ∞ (amplitudes j) (Usource) →
      (∀ y ∈ Usource, ∀ k, 1 ≤ k →
        ‖iteratedFDeriv ℝ k φ y‖ ≤ P k * Lpair^(k-1)) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k χ y‖ ≤ X k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k η y‖ ≤ Y k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes i) y‖ ≤ C k * Lpair^k) →
      (∀ y ∈ Usource, ∀ k, ‖iteratedFDeriv ℝ k (amplitudes j) y‖ ≤ C k * Lpair^k) →
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun z ↦ χ z •
          (if minus then ProductSum.minusSource phases amplitudes i j z
            else ProductSum.plusSource phases amplitudes i j z))) y)
      ∃ hg : MemLp g 2 volume, ∀ (r : ℕ) (Vout : Set E),
        let h := (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g
        let solution := localRealCompression isOpen_ball.measurableSet Vout
          (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr h)
        MemRestrictionSobolev Vout r solution ∧
          restrictionSobolevNorm Vout r solution ≤ D r * lam^r := by
  obtain ⟨Dcoeff, hDcoeff, hcoeff⟩ := exists_coefficient_pair_inverse_profile
    (n := d+1) center hnorm hbuffer AQ AB hAQ hAB
    (sectorLowOrder d + (d+2)) reserve hreserve
  obtain ⟨Dsource, hDsource, hsource⟩ := exists_reduced_signed_modulated_source_sobolev_constants
    (n := d+1) (N := N) hS P X Y AQ C hP hX hY hAQ hC hCfreq
  choose Cre hCre hre using fun r ↦ exists_source_quadrature_restriction_comparison (d := d) r
  let D := fun r ↦ responseCost r * (Cre r * Dsource r + Dcoeff r * (Cre 0 * Dsource 0))
  have hD r : 0 ≤ D r := mul_nonneg (hresponseCost r)
    (add_nonneg (mul_nonneg (hCre r) (hDsource r))
      (mul_nonneg (hDcoeff r).le (mul_nonneg (hCre 0) (hDsource 0))))
  refine ⟨D, hD, ?_⟩
  intro Lc Lpair lam ρ hLc hLcPair hLlam hρ hρlam Q B hQ hB hpQ hpB
    W uQ uB coeff β W₁ retarded Krecut Corr htame Usource hUsource hUprofile χ η phases amplitudes
    minus i j _hdiag φ hχ hχS hχU hη hφ hAi hAj hφb hχb hηb hAib hAjb g
  have hLpair : 1 ≤ Lpair := hLc.trans hLcPair
  have hlam : 0 ≤ lam := (zero_le_one.trans hLpair).trans hLlam
  have hQjets y (hy : y ∈ ball center profileRadius) k :
      ‖iteratedFDeriv ℝ k Q y‖ ≤ AQ k * Lpair^k := by
    apply (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _) (hQ.of_le (by simp))
      (ball_subset_closedBall hy) le_rfl).trans ((hpQ k).trans ?_)
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (zero_le_one.trans hLc) hLcPair _).trans
        (pow_le_pow_right₀ hLpair (Nat.sub_le _ _))) (hAQ k)
  have hprofile r : 1+coeff (r+β) ≤ Dcoeff r * lam^r := by
    have hc := hcoeff isOpen_univ (subset_univ _) Q B hQ hB Lc hLc hpQ hpB r
    have hc' : 1+coeff (r+β) ≤ Dcoeff r * Lc^r := by
      simpa only [coeff,uQ,uB,β,add_assoc] using hc
    exact hc'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hLc) (hLcPair.trans hLlam) _) (hDcoeff r).le)
  obtain ⟨hp, hm, hpm⟩ := hsource Usource hUsource
    Lpair lam ρ ρ hLpair hLlam hρ.le hρ.le hρlam hρlam χ η φ φ Q
    (amplitudes i) (amplitudes j) hχ hχS hχU hη hQ.contDiffOn hφ hφ hAi hAj
    hφb hφb hχb hηb (fun y hy k ↦ hQjets y (hUprofile hy) k) hAib hAjb
  have hfinish (v : E → V)
      (hv : MemLp (modulatedSource χ φ v ρ) 2 volume)
      (he : g = fun y ↦ euclideanRealPart (modulatedSource χ φ v ρ y))
      (hvbound : ∀ r : ℕ,
        MemVectorFourierSobolev (r : ℝ) (hv.toLp (modulatedSource χ φ v ρ)) ∧
          vectorFourierSobolevNorm (r : ℝ) (hv.toLp (modulatedSource χ φ v ρ)) ≤ Dsource r * lam^r) :
      ∃ hg : MemLp g 2 volume, ∀ (r : ℕ) (Vout : Set E),
        let h := (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g
        let solution := localRealCompression isOpen_ball.measurableSet Vout
          (pairedSolver f hK L₀ Q B output ho hob (retarded 0)) (Corr h)
        MemRestrictionSobolev Vout r solution ∧
          restrictionSobolevNorm Vout r solution ≤ D r * lam^r := by
    let z := hv.toLp (modulatedSource χ φ v ρ)
    let u := l2RealPart (volume.restrict W) (restrictL2 W z)
    have hrep : l2RealPart volume z =ᵐ[volume] g := by
      rw [he]
      filter_upwards [euclideanRealPart.coeFn_compLpL z, hv.coeFn_toLp] with y hr hz
      exact hr.trans (congrArg euclideanRealPart hz)
    have hg : MemLp g 2 volume := (Lp.memLp (l2RealPart volume z)).ae_eq hrep
    have heq : (hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g = u := by
      apply Lp.ext
      filter_upwards [(hg.mono_measure (Measure.restrict_le_self (s := W))).coeFn_toLp,
        euclideanRealPart.coeFn_compLpL (restrictL2 W z), restrictL2_coeFn W z,
        ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL z), ae_restrict_of_ae hrep]
          with y hg' hr hl hgr hgR
      change (l2RealPart (volume.restrict W) (restrictL2 W z)) y = _ at hr
      change (l2RealPart volume z) y = _ at hgr
      change _ = (l2RealPart (volume.restrict W) (restrictL2 W z)) y
      rw [hg', hr, hl, ← hgr, hgR]
    have hu r : MemRestrictionSobolev W r u ∧
        restrictionSobolevNorm W r u ≤ (Cre r * Dsource r) * lam^r := by
      obtain ⟨hm, hb⟩ := hre r z (hvbound r).1 W 1 (by simp)
      simp only [one_smul] at hm hb
      exact ⟨hm, (hb.trans (mul_le_mul_of_nonneg_left (hvbound r).2 (hCre r))).trans_eq
        (by ring)⟩
    have hlow : ‖u‖ ≤ Cre 0 * Dsource 0 := by
      simpa only [pow_zero, mul_one] using (norm_le_restrictionSobolevNorm (hu 0).1).trans (hu 0).2
    refine ⟨hg, fun r Vout ↦ ?_⟩
    dsimp only
    rw [heq]
    obtain ⟨hm, hb⟩ := htame r u (hu r).1 Vout
    refine ⟨hm, hb.trans ?_⟩
    calc
      _ ≤ responseCost r * ((Cre r * Dsource r) * lam^r +
          (Dcoeff r * lam^r) * (Cre 0 * Dsource 0)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hu r).2
          (mul_le_mul (hprofile r) hlow (norm_nonneg _) (mul_nonneg (hDcoeff r).le (pow_nonneg hlam _))))
          (hresponseCost r)
      _ = D r * lam^r := by dsimp only [D]; ring
  cases minus with
  | false =>
    exact hfinish _ hp
      (cutoff_stressSource_plus_eq_real_modulatedSource Q χ η phases amplitudes i j hρ.ne')
      (fun r ↦ (hpm r).1)
  | true =>
    exact hfinish _ hm
      (cutoff_stressSource_minus_eq_real_modulatedSource Q χ η phases amplitudes i j hρ.ne')
      (fun r ↦ (hpm r).2)

end JanetCartan.PhysicalPairs
