module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedProductRemainder
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RecutSourceInputs
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.LocalizedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Realization

/-!
# The normalized inverse remainder on the actual inner-cut product source

The finite expansion of the corrected source acts on the inner-bump datum.
Apply the existing inner-cutoff geometry producer and the proved normalized
product remainder to that literal datum. The original tensor cutoff can extend
beyond the measurement domain: only the inverse's inner bump must lie there.
No phase, amplitude, residual or inverse is selected again.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter
open scoped ContDiff ComplexConjugate NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.FiniteAssembly RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.FiniteEvolution
open RegularSector.Characteristic.EvolutionIntegral RegularSector.Characteristic.RetardedLocalization
open LocalSobolev FixedDomainInverse ArbitraryAccuracy SmallSupport
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.Complement.InactiveSource
open Sampling.BackgroundModulation ArbitraryAccuracy.ResidualLocalization JanetCartan.Localization
variable {d N : ℕ} {Ω : Set (Euclidean (d+1))} {center : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The finite remainder of the SAME normalized inverse has arbitrary original
stage decay on the actual inner-bump source. The existing localized-geometry
producer derives the product cutoff's phase geometry and derivative profile;
the existing product remainder derives negative source and coefficient costs.
The uncut original source is admitted from its literal normalized signed phase
and complete stress amplitude, with no source norm assumption. Only the inner
bump must be supported in the measured ball. Constants and depth precede sample
types, sources and histories, while the threshold precedes accuracy.
Both original source cutoffs, the auxiliary envelope, full `B`, both inverse
masks and doubled plus diagonal remain. Consumers:
`normalized_correctedSource_angular_finite_expansion` and
`UniformStep.SampledProduct` (`app:ch_regular:eq:inverse-remainder`,
`app:ch_pairs:eq:pairs-lag-one-error`). The same-family contraction and signed
gains are the normalized inverse constructor's published outputs. -/
theorem exists_normalized_innerCut_product_inverse_remainder_constants
    (f : ActualMaskFamily Ω center RQ A₀ K M) (hK : IsCompact K) (L₀ : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (χ₂ χ₃ : ContDiffBump center) (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {normRadius profileRadius : ℝ} (hnorm : 0 < normRadius) (hbuffer : normRadius < profileRadius)
    (hχ₂W : tsupport (χ₂ : E → ℝ) ⊆ ball center normRadius)
    {Ssrc Senv : Set E} (hSenv : IsCompact Senv)
    (hSenvU : Senv ⊆ ball center profileRadius)
    {a b cbeat θ : ℝ} (ha : 0 < a) (hbeat : 0 < cbeat) (hθ : θ < 1)
    (Cscale : ℝ) (P X Y Z AQ AB C Gain : ℕ → ℝ)
    (hY : ∀ r, 0 ≤ Y r) (hZ : ∀ r, 0 ≤ Z r)
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
      let uQ := smoothCoefficientL2 isOpen_univ hnorm
        (show closedBall center normRadius ⊆ Set.univ from subset_univ _) Q hQ.contDiffOn
      let uB := smoothCoefficientL2 isOpen_univ hnorm
        (show closedBall center normRadius ⊆ Set.univ from subset_univ _) B hB.contDiffOn
      let coeff := fun k ↦ restrictionSobolevNorm W k uQ + restrictionSobolevNorm W k uB
      let β := sectorLowOrder d + (d+2)
      ∀ (W₁ : f.centers → TwoTimeAmplitude d (d+1)) (retarded : H →L[ℂ] H),
      let Krecut := localRealCompression (U := W) isOpen_ball.measurableSet W
        (measuredOperator χ₂ χ₃ χ₂.continuous χ₃.continuous
          (bump_norm_le_one χ₂) (bump_norm_le_one χ₃)
          (pairedResidual f hK L₀ Q B output ho hob W₁ retarded))
      ‖Krecut‖ ≤ θ →
      (∀ (k : ℕ) (v : LocalL2 W E), MemRestrictionSobolev W k v →
        (MemRestrictionSobolev W (k+1) (Krecut v) ∧
          restrictionSobolevNorm W (k+1) (Krecut v) ≤ Gain (k+1) *
            (restrictionSobolevNorm W k v + (1+coeff (k+1+β))*‖v‖)) ∧
        (MemRestrictionSobolev W (k+1) (Krecut.adjoint v) ∧
          restrictionSobolevNorm W (k+1) (Krecut.adjoint v) ≤ Gain (k+1) *
            (restrictionSobolevNorm W k v + (1+coeff (k+1+β))*‖v‖))) →
      ∀ (ψ η : E → ℝ) (ι : Type*) (phases : ι → E → ℝ)
        (amplitudes : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ)
        (minus : Bool) (i k : ι), (minus = true → i ≠ k) →
      let φ := fun y ↦ (if minus then phases i y - phases k y else phases i y + phases k y) / ρ
      SourceGeometry χ φ Ssrc a b Lpair P X →
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Senv → EqOn ψ (fun _ ↦ 1) (tsupport χ) →
      ContDiffOn ℝ ∞ η (ball center profileRadius) →
      ContDiffOn ℝ ∞ (amplitudes i) (ball center profileRadius) →
      ContDiffOn ℝ ∞ (amplitudes k) (ball center profileRadius) →
      (∀ y ∈ ball center profileRadius, ∀ j, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Y j * Lpair^j) →
      (∀ y ∈ ball center profileRadius, ∀ j, ‖iteratedFDeriv ℝ j η y‖ ≤ Z j * Lpair^j) →
      (∀ y ∈ ball center profileRadius, ∀ j, ‖iteratedFDeriv ℝ j (amplitudes i) y‖ ≤ C j * Lpair^j) →
      (∀ y ∈ ball center profileRadius, ∀ j, ‖iteratedFDeriv ℝ j (amplitudes k) y‖ ≤ C j * Lpair^j) →
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun x ↦ χ x •
          (if minus then ProductSum.minusSource phases amplitudes i k x
            else ProductSum.plusSource phases amplitudes i k x))) y)
      ∃ hg : MemLp g 2 volume,
        let h := bumpL2 (p := 2) le_rfl χ₂
          ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
        MemRestrictionSobolev W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ∧
        restrictionSobolevNorm W s (neumannInverse Krecut ((Krecut^(depth+s)) h)) ≤
          D * ((R^carrierExponent * R^(-separationExponent))^q)⁻¹ := by
  obtain ⟨Xloc, hXloc, hgeometry⟩ := exists_innerCutoff_source_geometry_profiles χ₂ χ hχ
  let cut := (χ₂ : E → ℝ) * χ
  have hcutW : tsupport cut ⊆ ball center normRadius := tsupport_mul_subset_left.trans hχ₂W
  obtain ⟨Rmin, hmin, hconstants⟩ := exists_normalized_product_inverse_remainder_constants
    (N := N) (ι := Bool) (b := b) f hK L₀ output ho hob χ₂ χ₃ hnorm hbuffer hSenv hSenvU
    hcutW ha hbeat hθ Cscale P Xloc Y Z AQ AB C Gain hXloc hY hZ hAQ hAB hC hGain hreserve s
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨depth, D, hD, hbound⟩ := hconstants q
  refine ⟨depth, D, hD, ?_⟩
  intro R Lc Lpair ρ hR hLc hLcPair hslow hρ Q B hQ hB hpQ hpB
    W uQ uB coeff β W₁ retarded Krecut hKrecut hgain ψ η ι phases amplitudes
    minus i k _hdiag φ geometry hψ hψS hone hη hAi hAk hψb hηb hAib hAkb g
  let θpair : Bool → E → ℝ := fun b ↦ if b then phases k else phases i
  let Apair : Bool → E → Matrix (Fin N) (Fin (d+1)) ℂ :=
    fun b ↦ if b then amplitudes k else amplitudes i
  have hcutGeometry : SourceGeometry cut φ (tsupport cut) a b Lpair P Xloc :=
    hgeometry φ Ssrc a b Lpair P X geometry
  obtain ⟨hgc, htail⟩ := hbound R Lc Lpair ρ hR hLc hLcPair hslow hρ Q B hQ hB hpQ hpB
    W₁ retarded hKrecut hgain cut ψ η θpair Apair minus false true (by simp)
    hcutGeometry hψ hψS (fun y hy ↦ hone (tsupport_mul_subset_right hy))
    hη hAi hAk hψb hηb hAib hAkb
  have hχU : tsupport χ ⊆ ball center profileRadius := by
    intro y hy
    exact hSenvU (hψS (subset_tsupport ψ (by
      change ψ y ≠ 0
      rw [hone hy]
      norm_num)))
  have hχc : HasCompactSupport χ := geometry.compact.of_isClosed_subset
    (isClosed_tsupport _) geometry.support_subset
  have hRp : 0 < R := (by norm_num : (0 : ℝ) < 2).trans_le (hmin.trans hR)
  have hρpos : 0 < ρ := (mul_pos hbeat (by positivity)).trans_le hρ
  let amp := fun y ↦ η y • ((1/2 : ℝ) • complexStressContraction (Q y)
    (if minus then symmetricBilinearTensor (amplitudes i y) ((amplitudes k y).map conj)
      else symmetricBilinearTensor (amplitudes i y) (amplitudes k y)))
  have hamp : ContDiffOn ℝ ∞ amp (ball center profileRadius) := by
    obtain ⟨hp, hm⟩ := contDiffOn_reduced_signed_amplitudes hQ.contDiffOn hη hAi hAk
    cases minus
    · exact hp
    · exact hm
  let fc := modulatedSource χ φ amp ρ
  have hfc : MemLp fc 2 volume := by
    have hh := memLp_carrier_source isOpen_ball ρ φ (fun y ↦ χ y • amp y)
      geometry.phase_smooth.contDiffOn (hχ.contDiffOn.smul hamp)
      ((tsupport_smul_subset_left _ _).trans hχU) (hχc.smul_right (f' := amp))
    have he : (fun y ↦ carrier ρ φ y • (χ y • amp y)) = fc := by
      funext y
      exact smul_comm _ _ _
    rwa [he] at hh
  have he : g = fun y ↦ euclideanRealPart (fc y) := by
    cases minus
    · exact cutoff_stressSource_plus_eq_real_modulatedSource Q χ η phases amplitudes i k hρpos.ne'
    · exact cutoff_stressSource_minus_eq_real_modulatedSource Q χ η phases amplitudes i k hρpos.ne'
  have hrep : l2RealPart volume (hfc.toLp fc) =ᵐ[volume] g := by
    rw [he]
    filter_upwards [euclideanRealPart.coeFn_compLpL (hfc.toLp fc), hfc.coeFn_toLp] with y hr hv
    exact hr.trans (congrArg euclideanRealPart hv)
  have hg : MemLp g 2 volume := (Lp.memLp (l2RealPart volume (hfc.toLp fc))).ae_eq hrep
  refine ⟨hg, ?_⟩
  dsimp only
  rw [innerCut_signed_product_source_local_eq Q χ η phases amplitudes minus i k χ₂ hg hgc]
  exact htail

end JanetCartan.SignedProductEstimates
