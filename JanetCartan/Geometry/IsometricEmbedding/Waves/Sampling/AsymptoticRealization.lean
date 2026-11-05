module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.KernelRealization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AsymptoticRealization.Bounds

/-!
# Source-scale sampling for the actual grouped kernel input

This is the conditional asymptotic deduction in
`app:ch_waves:eq:sampling-all-prefixes` and `app:ch_waves:thm:sampling`.
The input is literally `RefinedInput n (cutoffCount Λ)`; both refined shells
use the kernel at their original band index. Constants and thresholds precede
both the frequency and the arbitrary additional data index.

The actual raw-wave producer must supply the uniform squared kernel constants
and the sharp restricted-operator estimate. The full-normal construction must
supply the largest continuum mean bound. These three primitive bounds are the
only analytic estimates assumed here, and are required only for `Λ ≥ 1`.
Instantiating them with the actual waves remains the responsibility of
`jc-simultaneous-sampling`; this module does not assert the unconditional source
theorem. No row, trace, concentration, or successful-event premise is assumed.
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
    ‖(D Λ σ a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤ C_op * refinedRadius i)
  (hmean : ∀ Λ, 1 ≤ Λ → ∀ σ,
    ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) (samplingMesh ε Λ)
      (fun c z ↦ refinedKernelPrefix (D Λ σ a) (cutoffCount Λ) (c, z))‖ ≤ C_mean)

include hn hc hs hm hkpos hk hp hψ hψc hε hQ hkernel hC_op hband hmean

private theorem source_estimates :
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
      operatorBernstein_refinedKernelPrefix (D Λ σ) hn L hw hψ hψc hwc hh hh₁ hC_op
        (hband Λ hΛ σ) hblock hR hC hmean' hscale.1 hscale.2.2.1

/-- Uniform source-scale failure bound for all grouped prefixes, on the actual
varying refined input (`app:ch_waves:eq:sampling-all-prefixes`). The constants
and the eventual threshold are chosen before `Λ` and the data index `σ`. -/
theorem eventually_refinedKernelPrefix_failure_le :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Λ : ℝ in atTop, ∀ σ,
      familyShiftLaw A p B (samplingMesh ε Λ)
        (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
          (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a c z ↦ refinedKernelPrefix (D Λ σ a) L (c, z)))
          (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (56 * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
  obtain ⟨c, hcp, he⟩ := source_estimates D hn hc hs hm hkpos hk hp hψ hψc
    hε hQ hkernel hC_op hband hmean
  exact ⟨c, hcp, he.mono fun _ h σ ↦ (h.2.2 σ).2⟩

/-- The actual varying-input failure probability tends to zero even when the
additional data are chosen separately at each frequency
(`app:ch_waves:eq:sampling-all-prefixes`). No small-frequency bound is needed. -/
theorem tendsto_refinedKernelPrefix_failure_zero (σ : ℝ → S) :
    Tendsto (fun Λ ↦ familyShiftLaw A p B (samplingMesh ε Λ)
      (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
        (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
          (fun a c z ↦ refinedKernelPrefix (D Λ (σ Λ) a) L (c, z)))
        (samplingTolerance ε Λ))ᶜ) atTop (𝓝 0) := by
  obtain ⟨c, hcp, hb⟩ := eventually_refinedKernelPrefix_failure_le D hn hc hs hm hkpos hk hp
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
theorem tendsto_refinedKernelPrefix_probability_one (σ : ℝ → S) :
    Tendsto (fun Λ ↦ (familyShiftLaw A p B (samplingMesh ε Λ)).real
      (allPrefixesGood (Finset.range (cutoffCount Λ + 1))
        (fun L ↦ familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
          (fun a c z ↦ refinedKernelPrefix (D Λ (σ Λ) a) L (c, z)))
        (samplingTolerance ε Λ))) atTop (𝓝 1) := by
  have hf := tendsto_refinedKernelPrefix_failure_zero D hn hc hs hm hkpos hk hp
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
theorem exists_threshold_refinedKernelPrefix_realization
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
  obtain ⟨c, hcp, he⟩ := source_estimates D hn hc hs hm hkpos hk hp hψ hψc
    hε hQ hkernel hC_op hband hmean
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
  have hα := blockConstant_pos (p := p) hψ hC_op
  have hC := meanConstant_bounds (n := n) (p := p) (C_mean := C_mean) hψ hQ
  have hR : 0 < blockConstant p P C_op * (Λ * samplingMesh ε Λ ^ 3) := by positivity
  have ht : 0 < samplingTolerance ε Λ := Real.rpow_pos_of_pos hΛpos _
  apply exists_refinedKernelPrefix_realization hc hs hm hkpos hk hp (D Λ σ) hn hψ hψc
    hh hh₁ hC_op (hband Λ hΛone σ) (block_le hψ hC_op hΛone hh.le) hR hC.1
    ((hmean Λ hΛone σ).trans hC.2) ht he.2.1
  exact ((he.2.2 σ).1).trans_lt (ENNReal.ofReal_lt_one.mpr hsmall)

end JanetCartan.Sampling
