module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.LocalizedRealization

/-!
# A sampling threshold before the kernel witnesses

The actual retained construction chooses its kernel at the given frequency.
This quantifier form of the support-local realization theorem chooses the
threshold from the same fixed three constants before that kernel is selected.
It is consumed by `MeasuredAmplitude.LocalRealization`; its analytic premises
are discharged there from the actual measured coefficients. It is only a
probabilistic deduction, not the construction of the source waves.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace JanetCartan.Sampling
open SeparatedSampling Realization RawInputPartition SamplingKernelBounds LatticeQuadrature
open BackgroundQuadrature AsymptoticRealization

variable {A : Type*} [Fintype A] {n p : ℕ}
  (hn : 1 ≤ n)
  {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
  (hm : ∫ t, κ t = 1) (hkpos : ∀ t, 0 ≤ κ t)
  (hk : Function.support κ ⊆ Set.Icc (-(1 / 4)) (1 / 4)) (hp : 0 < p)
  {ψ : A → Point → ℝ} {B C_op C_mean ε : ℝ} {P Q : A → ℝ}
  (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
  (hε : 0 < ε) (hQ : ∀ a, 0 ≤ Q a) (hC_op : 0 ≤ C_op)

include hn hc hs hm hkpos hk hp hψ hψc hε hQ hC_op

/-- A uniform threshold precedes the actual kernel witnesses at each frequency.
The support-local bound is sufficient for the original weighted event; zero
channels retain positive upper Bernstein parameters
(`app:ch_waves:eq:sampling-all-prefixes`). -/
theorem exists_uniform_refinedKernelPrefix_threshold_of_support
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ ≥ Λ₀,
      ∀ D : A → BandKernelData
        (Fin (cutoffCount Λ) × ((Fin 3 → Fin (p + 1)) × Point)) n,
      (∀ a, (D a).squaredKernelConstant ≤ Q a) →
      (∀ a (i : RefinedIndex (cutoffCount Λ)) c z,
        ψ a z ≠ 0 → ‖(D a).operator (refinedRadius i) (i.1, (c, z))‖ ^ 2 ≤
          C_op * refinedRadius i) →
      ‖∑ a, patchMeanNormal p B (ψ a) (convolvedBoxWindow κ p) (samplingMesh ε Λ)
        (fun c z ↦ refinedKernelPrefix (D a) (cutoffCount Λ) (c, z))‖ ≤ C_mean →
      ∃ ξ : A → ShiftSpace p B (samplingMesh ε Λ),
        (∀ a q i, 0 ≤ extendedShift (ξ a) q i ∧
          extendedShift (ξ a) q i < samplingMesh ε Λ) ∧
        (∀ L ≤ cutoffCount Λ,
          ‖familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
            (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤
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
  let α := blockConstant p P C_op
  let C := meanConstant n p B P Q C_mean
  have hα : 0 < α := blockConstant_pos hψ hC_op
  have hC : 0 < C := (meanConstant_bounds hψ hQ).1
  have hmeanC : C_mean ≤ C := (meanConstant_bounds hψ hQ).2
  obtain ⟨c, hcp, hscale⟩ := eventually_sampling_bernstein_scale hα hC hε
  have hsmall := (tendsto_sampling_failure_bound 56 c ε n hcp hε).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨Λ₁, hΛ₁⟩ := eventually_atTop.mp (hscale.and hsmall)
  refine ⟨max 1 Λ₁, le_max_left _ _, fun Λ hΛ D hkernel hband hmean ↦ ?_⟩
  have hΛone : 1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛone
  obtain ⟨hscale, hsmall⟩ := hΛ₁ Λ ((le_max_right _ _).trans hΛ)
  have hh : 0 < samplingMesh ε Λ := Real.rpow_pos_of_pos hΛpos _
  have hh₁ : samplingMesh ε Λ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛone (by linarith)
  let R := α * (Λ * samplingMesh ε Λ ^ 3)
  let t := samplingTolerance ε Λ
  have hR : 0 < R := by dsimp [R]; positivity
  change 0 < t ∧ 0 < C * R ∧ C * R + R * t / 3 ≤ t ^ 2 ∧
    c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (C * R + R * t / 3)) at hscale
  rw [mul_comm C R] at hscale
  have htrace := traceBound_bounds (C_mean := C_mean) hΛone D hψ hQ hkernel
  have hblock := block_le (p := p) hψ hC_op hΛone hh.le
  let := isProbabilityMeasure_familyShiftLaw (J := A) p B hh
  have hwc := (contDiff_convolvedBoxWindow hc hs p).continuous
  have hw := convolvedBoxWindow_bounds (hs.continuous.integrable_of_hasCompactSupport hc)
    hm hkpos hk hp
  let Δ L := familyDeviation p B ψ (convolvedBoxWindow κ p) (samplingMesh ε Λ)
    (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))
  let good := allPrefixesGood (Finset.range (cutoffCount Λ + 1)) Δ t
  have hmeas : MeasurableSet good := measurableSet_familyGood B _ hψc hwc _ _
    (fun L a c ↦ (continuous_refinedKernelPrefix (D a) L).comp
      (continuous_const.prodMk continuous_id)) _
  have hprob := allPrefixes_failure_le_of_bernstein
    (familyShiftLaw A p B (samplingMesh ε Λ)) (Finset.range (cutoffCount Λ + 1)) Δ
    (fun _ ↦ R * traceBound D B P) n hΛpos.le hscale.2.1
    (cutoffCount_prefix_card_le hΛone)
    (fun _ _ ↦ ⟨mul_nonneg hR.le htrace.1, by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htrace.2 hR.le⟩)
    hscale.2.2.2 (fun L _ ↦ ?_)
  · norm_num only at hprob
    have hbad : familyShiftLaw A p B (samplingMesh ε Λ) goodᶜ < 1 :=
      hprob.trans_lt (ENNReal.ofReal_lt_one.mpr hsmall)
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
  · simpa only [OperatorCompression.bernsteinTail, traceBound, R, α, neg_div] using
      operatorBernstein_refinedKernelPrefix_of_support D hn L hw hψ hψc hwc hh hh₁ hC_op
        hband hblock hR hC (hmean.trans hmeanC) hscale.1 hscale.2.2.1

end JanetCartan.Sampling
