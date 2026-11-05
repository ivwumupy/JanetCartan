module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported
public import JanetCartan.Analysis.Microlocal.NormalizedResidualWords.ObservedChains.SourceSupport

/-!
# The actual signed source's low norm in the observed residual chain

The complete tensor and stress amplitudes supply the zeroth envelope bound.
Modulation preserves that bound, including short differences and doubled sums.
Compact support then proves real L² admission and a constant independent of
carrier frequency, separation, proof depth and accuracy. The original inner
bump, zero extension and complex inclusion supply the literal chronological
source of `ObservedChains.measuredResidual_hchain_of_individual_estimates`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseTransfer ResponseTransfer.SourceNegative Sampling.BackgroundModulation
open PrimarySourceAdmission LocalSobolev SmallSupport
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.NormalizedResidualWords.ObservedChains
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
variable {d N : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))
local notation "RV" => EuclideanSpace ℝ (Fin (d+1))

/-- The original signed `ProductSum` source and its literal cut/complex chain
datum have a uniform low norm. Apply the existing complete reduced-amplitude
jet estimate at order zero, the unit-modulus carrier identity, and finite
support integration. Both source cutoffs and the half stress contraction
remain; no source norm, normalized phase bound, frequency or accuracy is an
input. This supplies `hu` and `hsupport` of
`ObservedChains.measuredResidual_hchain_of_individual_estimates` on the same
source used by `normalized_correctedSource_angular_finite_expansion`.
The amplitude and row profiles are supplied by the canonical/history producers
(`app:ch_pairs:eq:pairs-lag-envelope`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_signed_product_source_chain_low_constant
    {S : Set E} (hS : IsCompact S)
    (X Y CQ C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set E), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ (χ η : E → ℝ) (Q : E → Fin (d+1) → MetricTensor (d+1)),
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
      ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ y‖ ≤ X r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η y‖ ≤ Y r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q y‖ ≤ CQ r * L^r) →
      ∀ (ι : Type*) (θ : ι → E → ℝ)
        (A : ι → E → Matrix (Fin N) (Fin (d+1)) ℂ) (i k : ι),
      ContDiffOn ℝ ∞ (θ i) U → ContDiffOn ℝ ∞ (θ k) U →
      ContDiffOn ℝ ∞ (A i) U → ContDiffOn ℝ ∞ (A k) U →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (A i) y‖ ≤ C r * L^r) →
      (∀ y ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (A k) y‖ ≤ C r * L^r) →
      ∀ minus : Bool,
      let g := fun y ↦ WithLp.toLp 2 (AmbientResponse.cutoffSource η
        (AmbientResponse.stressSource Q (fun x ↦ χ x •
          (if minus then ProductSum.minusSource θ A i k x
            else ProductSum.plusSource θ A i k x))) y)
      ∃ hg : MemLp g 2 volume, ‖hg.toLp g‖ ≤ D ∧
        ∀ (W : Set E) (hW : MeasurableSet W) (center : E) (χ₂ : ContDiffBump center),
          let u := bumpL2 (p := 2) le_rfl χ₂
            ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
          (∀ᵐ y ∂volume.restrict W, y ∉ tsupport (χ₂ : E → ℝ) → u y = 0) ∧
          ‖u‖ ≤ D ∧
          ‖restrictL2 univ (l2ComplexInclusion volume (zeroExtend hW u))‖ ≤ D := by
  obtain ⟨J, hJ, hjets⟩ := exists_cutoff_reduced_signed_jet_constants
    (n := d+1) (N := N) X Y CQ C hX hY hCQ hC
  refine ⟨J 0 * Real.sqrt (volume.real S), mul_nonneg (hJ 0) (Real.sqrt_nonneg _), ?_⟩
  intro U hU L hL χ η Q hχ hχS hχU hη hQ hχb hηb hQb
    ι θ A i k hθi hθk hAi hAk hAib hAkb minus g
  obtain ⟨hplus, hminus⟩ := contDiffOn_reduced_signed_amplitudes hQ hη hAi hAk
  have hjet := hjets U hU L hL χ η Q (A i) (A k) hχ.contDiffOn
    hη hQ hAi hAk hχb hηb hQb hAib hAkb
  let φ := fun y ↦ if minus then θ i y - θ k y else θ i y + θ k y
  let amp := fun y ↦ η y • ((1 / 2 : ℝ) • complexStressContraction (Q y)
    (if minus then symmetricBilinearTensor (A i y) ((A k y).map conj)
      else symmetricBilinearTensor (A i y) (A k y)))
  have hφ : ContDiffOn ℝ ∞ φ U := by
    cases minus <;> simp only [φ, Bool.false_eq_true, ↓reduceIte]
    · exact hθi.add hθk
    · exact hθi.sub hθk
  have hamp : ContDiffOn ℝ ∞ amp U := by
    cases minus <;> simp only [amp, Bool.false_eq_true, ↓reduceIte]
    · exact hplus
    · exact hminus
  let z := modulatedSource χ φ amp 1
  have hz : g = fun y ↦ euclideanRealPart (z y) := by
    cases minus
    · simpa only [g, z, φ, amp, Bool.false_eq_true, ↓reduceIte, div_one] using
        cutoff_stressSource_plus_eq_real_modulatedSource Q χ η θ A i k (ρ := 1) one_ne_zero
    · simpa only [g, z, φ, amp, ↓reduceIte, div_one] using
        cutoff_stressSource_minus_eq_real_modulatedSource Q χ η θ A i k (ρ := 1) one_ne_zero
  have hcarrier : ContDiffOn ℝ ∞ (carrier 1 φ) U := by
    change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((1 * φ y : ℝ) : ℂ))) U
    exact (contDiffOn_const.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
  have hzs : ContDiff ℝ ∞ z :=
    contDiff_cutoff_of_support_subset hχ hU (hcarrier.smul hamp) hχU
  have hgs : ContDiff ℝ ∞ g := by
    rw [hz]
    exact euclideanRealPart.contDiff.comp hzs
  have hzero (y : E) (hy : y ∉ S) : g y = 0 := by
    have hc : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχS h))
    rw [hz]
    simp only [z, modulatedSource, hc, zero_smul, map_zero]
  have hg : MemLp g 2 volume :=
    hgs.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hzero)
  have hbound (y : E) : ‖g y‖ ≤ J 0 := by
    by_cases hy : y ∈ U
    · have ha : ‖χ y • amp y‖ ≤ J 0 := by
        have hj := hjet y hy 0
        cases minus
        · simpa only [amp, Bool.false_eq_true, ↓reduceIte, norm_iteratedFDeriv_zero,
            pow_zero, mul_one] using hj.1
        · simpa only [amp, ↓reduceIte, norm_iteratedFDeriv_zero, pow_zero, mul_one] using hj.2
      calc
        ‖g y‖ ≤ ‖z y‖ := by
          rw [hz]
          simpa only [one_mul] using euclideanRealPart.le_of_opNorm_le
            (euclideanRealPart_norm_le (ι := Fin (d+1))) (z y)
        _ = ‖χ y • amp y‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact norm_modulatedSource χ φ amp 1 y
        _ ≤ J 0 := ha
    · have hc : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχU h))
      rw [hz]
      simpa only [z, modulatedSource, hc, zero_smul, map_zero, norm_zero] using hJ 0
  have hnorm : ‖hg.toLp g‖ ≤ J 0 * Real.sqrt (volume.real S) := by
    have h : ‖hg.toLp g‖ ≤
        ‖indicatorConstLp (μ := volume) 2 hS.measurableSet hS.measure_ne_top (J 0)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hg.coeFn_toLp, indicatorConstLp_coeFn (μ := volume) (p := 2)
        (hs := hS.measurableSet) (hμs := hS.measure_ne_top) (c := J 0)] with y hy hi
      rw [hy, hi]
      by_cases hyS : y ∈ S
      · simpa only [indicator_of_mem hyS, Real.norm_eq_abs, abs_of_nonneg (hJ 0)] using hbound y
      · simp only [indicator_of_notMem hyS, hzero y hyS, norm_zero, le_refl]
    convert h using 1
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hJ 0), ENNReal.toReal_ofNat,
      Real.sqrt_eq_rpow, one_div]
  refine ⟨hg, hnorm, ?_⟩
  intro W hW center χ₂ u
  have hlocal : ‖(hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g‖ ≤ ‖hg.toLp g‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hcut : ‖u‖ ≤ J 0 * Real.sqrt (volume.real S) := by
    have hbump : ‖u‖ ≤ 1 *
        ‖(hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g‖ :=
      (bumpL2 (F := RV) (μ := volume.restrict W) (p := 2) le_rfl χ₂).le_of_opNorm_le
        (norm_bumpL2_two_le_one (F := RV) (μ := volume.restrict W) χ₂)
        ((hg.mono_measure (Measure.restrict_le_self (s := W))).toLp g)
    simp only [one_mul] at hbump
    exact hbump.trans (hlocal.trans hnorm)
  exact ⟨cut_source_ae_zero_off_support χ₂ _, hcut, (complex_source_norm_le hW u).trans hcut⟩

end JanetCartan.SignedProductEstimates
