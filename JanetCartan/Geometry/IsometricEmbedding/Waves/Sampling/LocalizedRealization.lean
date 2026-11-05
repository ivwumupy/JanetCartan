module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AsymptoticRealization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LocalizedRealization.KernelConcentration

/-!
# Source-scale realization from bounds on the actual patch support

The support-local version of `exists_threshold_refinedKernelPrefix_realization`
for `app:ch_waves:thm:sampling` and `app:ch_waves:eq:sampling-all-prefixes`.
The sharp channel estimate is required only when the ORIGINAL patch weight
is nonzero. All conclusions use the original `D`, refined input, grouped
prefixes, entire output, samples, weights, and shift law. In particular both
physical real quadratures are retained. The same shifts work for every later
background family satisfying its stated derivative bound.

The uniform squared-kernel and largest-mean bounds remain explicit inputs,
produced by `MeasuredAmplitude.FullNormalData`; the local sharp estimate is
produced by `MeasuredAmplitude.exists_uniform_retained_measuredBand_bound` in
`MeasuredAmplitude.UniformBandBounds`. Instantiating these three estimates on
the actual finite chart family belongs to `jc-simultaneous-sampling`. No
successful event, variance, trace, or concentration estimate is assumed here.
Constants and the threshold precede frequency and arbitrary additional data.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace JanetCartan.Sampling
open SeparatedSampling Realization RawInputPartition SamplingKernelBounds LatticeQuadrature
open BackgroundQuadrature AsymptoticRealization

variable {A S : Type*} [Fintype A] {n p : ℕ}
  (D : (Λ : ℝ) → S → A →
    BandKernelData (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n)
  (hn : 1 ≤ n)
  {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
  (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
  (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
  {ψ : A → Point → ℝ} {B C_op C_mean ε : ℝ} {P Q : A → ℝ}
  (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
  (hε : 0 < ε) (hQ : ∀ a, 0 ≤ Q a)
  (hkernel : ∀ Λ, 1 ≤ Λ → ∀ σ a, (D Λ σ a).squaredKernelConstant ≤ Q a)
  (hC_op : 0 ≤ C_op)
  (hband : ∀ Λ, 1 ≤ Λ → ∀ σ a (i : RefinedIndex (cutoffCount Λ)) c z,
    ψ a z ≠ 0 → ‖(D Λ σ a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
  (hmean : ∀ Λ, 1 ≤ Λ → ∀ σ,
    ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) (samplingMesh ε Λ)
      (fun c z ↦ refinedKernelPrefix (D Λ σ a) (cutoffCount Λ) (c, z))‖ ≤ C_mean)

include hn hc hs hm hkpos hk hp hψ hψc hε hQ hkernel hC_op hband hmean

private theorem localized_source_estimates :
    let α := blockConstant p P C_op
    let C := meanConstant n p B P Q C_mean
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Λ : ℝ in atTop,
      let R := α * (Λ * samplingMesh ε Λ ^ 3)
      let t := samplingTolerance ε Λ
      1 ≤ Λ ∧ (R * C + R * t / 3 ≤ t ^ 2) ∧ ∀ σ,
        ((cutoffCount Λ + 1 : ENNReal) * OperatorCompression.bernsteinTail R (R * C)
          (R * traceBound (D Λ σ) B P) t ≤
            ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)))) ∧
        (familyShiftLaw A p B (samplingMesh ε Λ)
          (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
            (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
              (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z))) t)ᶜ ≤
            ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)))) := by
  let α := blockConstant p P C_op
  let C := meanConstant n p B P Q C_mean
  have hα : 0 < α := blockConstant_pos hψ hC_op
  have hC : 0 < C := (meanConstant_bounds hψ hQ).1
  have hmeanC : C_mean ≤ C := (meanConstant_bounds hψ hQ).2
  obtain ⟨c, hcp, hscale⟩ := eventually_sampling_bernstein_scale hα hC hε
  refine ⟨c, hcp, ?_⟩
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  filter_upwards [eventually_ge_atTop (1 : ℝ), hscale] with Λ hΛ hscale
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
  have hh₁ : samplingMesh ε Λ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  let R := α * (Λ * samplingMesh ε Λ ^ 3)
  let t := samplingTolerance ε Λ
  have hR : 0 < R := by dsimp [R]; positivity
  change 0 < t ∧ 0 < C * R ∧ C * R + R * t / 3 ≤ t ^ 2 ∧
    c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (C * R + R * t / 3)) at hscale
  rw [mul_comm C R] at hscale
  refine ⟨hΛ, hscale.2.2.1, fun σ ↦ ?_⟩
  have htrace := traceBound_bounds (C_mean := C_mean) hΛ (D Λ σ) hψ hQ (hkernel Λ hΛ σ)
  have hblock := block_le (p := p) hψ hC_op hΛ hh.le
  have hmean' := (hmean Λ hΛ σ).trans hmeanC
  refine ⟨cutoff_bernsteinTail_le hΛ hR hC htrace.2 hscale.2.2.2, ?_⟩
  have hprob := allPrefixes_failure_le_of_bernstein
    (familyShiftLaw A p B (samplingMesh ε Λ)) (Finset.range (cutoffCount Λ + 1))
    (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
      (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z)))
    (fun _ ↦ R * traceBound (D Λ σ) B P) n hΛpos.le hscale.2.1
    (cutoffCount_prefix_card_le hΛ)
    (fun _ _ ↦ ⟨mul_nonneg hR.le htrace.1, by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htrace.2 hR.le⟩)
    hscale.2.2.2 (fun L _ ↦ ?_)
  · norm_num only at hprob
    exact hprob
  · simpa only [OperatorCompression.bernsteinTail, traceBound, R, α, neg_div] using
      operatorBernstein_refinedKernelPrefix_of_support (D Λ σ) hn L hw hψ hψc hwc hh hh₁ hC_op
        (hband Λ hΛ σ) hblock hR hC hmean' hscale.1 hscale.2.2.1

/-- Uniform source-scale failure bound for all grouped prefixes, on the actual
varying refined input (`app:ch_waves:eq:sampling-all-prefixes`). The constants
and the eventual threshold are chosen before `Λ` and the data index `σ`. -/
theorem eventually_refinedKernelPrefix_failure_le_of_support :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Λ : ℝ in atTop, ∀ σ,
      familyShiftLaw A p B (samplingMesh ε Λ)
        (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
          (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z)))
          (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
  obtain ⟨c, hcp, he⟩ := localized_source_estimates D hn hc hs hm hkpos hk hp hψ hψc
    hε hQ hkernel hC_op hband hmean
  exact ⟨c, hcp, he.mono fun _ h σ ↦ (h.2.2 σ).2⟩

/-- The actual varying-input failure probability tends to zero even when the
additional data are chosen separately at each frequency
(`app:ch_waves:eq:sampling-all-prefixes`). No small-frequency bound is needed. -/
theorem tendsto_refinedKernelPrefix_failure_zero_of_support (σ : ℝ → S) :
    Tendsto (fun Λ ↦ familyShiftLaw A p B (samplingMesh ε Λ)
      (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
        (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
          (fun a c z ↦ refinedKernelPrefix (D Λ (σ Λ) a) L (c, z)))
        (samplingTolerance ε Λ))ᶜ) atTop (𝓝 0) := by
  obtain ⟨c, hcp, hb⟩ := eventually_refinedKernelPrefix_failure_le_of_support D hn hc hs hm hkpos hk hp
    hψ hψc hε hQ hkernel hC_op hband hmean
  have ht := ENNReal.tendsto_ofReal (tendsto_sampling_failure_bound 56 c ε n hcp hε)
  simp only [ENNReal.ofReal_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.mp ht δ hδ] with Λ hb ht
  exact (hb (σ Λ)).trans ht

/-- Probability tending to one for all grouped prefixes on the changing input
`RefinedInput n (cutoffCount Λ)`, uniformly enough to allow any frequency-dependent
data choice (`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem tendsto_refinedKernelPrefix_probability_one_of_support (σ : ℝ → S) :
    Tendsto (fun Λ ↦ (familyShiftLaw A p B (samplingMesh ε Λ)).real
      (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
        (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
          (fun a c z ↦ refinedKernelPrefix (D Λ (σ Λ) a) L (c, z)))
        (samplingTolerance ε Λ))) atTop (𝓝 1) := by
  have hf := tendsto_refinedKernelPrefix_failure_zero_of_support D hn hc hs hm hkpos hk hp
    hψ hψc hε hQ hkernel hC_op hband hmean σ
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hf
  simp only [ENNReal.toReal_zero] at hr
  have ht := tendsto_const_nhds.sub hr (a := (1 : ℝ))
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _
  let := isProbabilityMeasure_familyShiftLaw (J := A) p B hh
  have hmeas := measurableSet_familyGood B (samplingMesh ε Λ) hψc
    (contDiff_convolvedBoxWindow hc hs p).continuous (Finset.range (cutoffCount Λ + 1))
    (fun L a c z ↦ refinedKernelPrefix (D Λ (σ Λ) a) L (c, z))
    (fun L a c ↦ (continuous_refinedKernelPrefix (D Λ (σ Λ) a) L).comp
      (continuous_const.prodMk continuous_id)) (samplingTolerance ε Λ)
  change 1 - (familyShiftLaw A p B (samplingMesh ε Λ)).real _ᶜ = _
  rw [measureReal_compl hmeas, probReal_univ]
  ring

/-- A threshold fixed before frequency and data gives one admissible separated
sample controlling every grouped prefix, with universal background quadrature
on those same shifts (`app:ch_waves:thm:sampling`,
`app:ch_waves:eq:sampling-all-prefixes`, `app:ch_waves:eq:background-quadrature`).
Only the primitive kernel, restricted-operator and full-normal bounds above
must be instantiated by the actual wave construction. -/
theorem exists_threshold_refinedKernelPrefix_realization_of_support
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ ≥ Λ₀, ∀ σ,
      ∃ ξ : A → ShiftSpace p B (samplingMesh ε Λ),
        (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧
          extendedShift (ξ a) q i < samplingMesh ε Λ) ∧
        (∀ L ≤ cutoffCount Λ,
          ‖familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z)) ξ‖ ≤
              samplingTolerance ε Λ) ∧
        (∀ a, SampleGeometry p B (P a) 1 (ψ a) (convolvedBoxWindow κ p)
          (samplingMesh ε Λ) (extendedShift (ξ a))) ∧
        (∀ (G : A → (Fin 3 → Fin (p + 1)) → Point → V) (Q_bg : A → ℝ),
          (∀ a c, ContDiff ℝ p (fun z ↦ ψ a z • G a c z)) →
          (∀ a, 0 ≤ Q_bg a) →
          (∀ a c z, ‖iteratedFDeriv ℝ p (fun z ↦ ψ a z • G a c z) z‖ ≤ Q_bg a) →
          ‖familyBackgroundError p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a ↦ extendedShift (ξ a)) G‖ ≤
              backgroundQuadratureConstant p B * (∑ a, Q_bg a) * samplingMesh ε Λ ^ p) := by
  obtain ⟨c, hcp, he⟩ := eventually_refinedKernelPrefix_failure_le_of_support D hn hc hs
    hm hkpos hk hp hψ hψc hε hQ hkernel hC_op hband hmean
  have hsmall := (tendsto_sampling_failure_bound 56 c ε n hcp hε).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨Λ₁, hΛ₁⟩ := eventually_atTop.mp (he.and hsmall)
  refine ⟨max 1 Λ₁, le_max_left _ _, fun Λ hΛ σ ↦ ?_⟩
  have hΛone : 1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛone
  obtain ⟨he, hsmall⟩ := hΛ₁ Λ ((le_max_right _ _).trans hΛ)
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
  have hh₁ : samplingMesh ε Λ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛone (by linarith)
  let := isProbabilityMeasure_familyShiftLaw (J := A) p B hh
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  let Δ L := familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
    (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z))
  let good := allPrefixesGood (Finset.range (cutoffCount Λ + 1)) Δ (samplingTolerance ε Λ)
  have hmeas : MeasurableSet good := measurableSet_familyGood B _ hψc hwc _ _
    (fun L a c ↦ (continuous_refinedKernelPrefix (D Λ σ a) L).comp
      (continuous_const.prodMk continuous_id)) _
  have hbad : familyShiftLaw A p B (samplingMesh ε Λ) goodᶜ < 1 :=
    (he σ).trans_lt (ENNReal.ofReal_lt_one.mpr hsmall)
  have hgood : 0 < familyShiftLaw A p B (samplingMesh ε Λ) good := by
    by_contra hz
    have hz' : familyShiftLaw A p B (samplingMesh ε Λ) good = 0 :=
      le_antisymm (not_lt.mp hz) bot_le
    rw [prob_compl_eq_one_sub hmeas, hz', tsub_zero] at hbad
    exact lt_irrefl _ hbad
  have hreal : 0 < (familyShiftLaw A p B (samplingMesh ε Λ)).real good :=
    ENNReal.toReal_pos hgood.ne' (measure_ne_top _ _)
  obtain ⟨ξ, hξgood, hξ⟩ := exists_mem_of_positive_of_ae _ hreal
    (ae_admissible_familyShift (J := A) (p := p) (B := B) hh)
  refine ⟨ξ, hξ, ?_, ?_, ?_⟩
  · intro L hL
    exact hξgood L (Finset.mem_range.mpr (Nat.lt_succ_of_le hL))
  · intro a
    exact sampleGeometry_of_admissible hw (hψ a) hh hh₁ _ (hξ a)
  · intro G Q_bg hG hQ_bg hderiv
    exact norm_familyBackgroundError_le hc hs hm hkpos hk hp hψ G hG Q_bg hQ_bg hderiv
      hh hh₁ _ hξ

end JanetCartan.Sampling
