module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Basic

/-!
# Finite-support L² bounds

The Hilbert–Schmidt alternative to Schur's inequality in the common kernel
estimate of `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A measurable finite-support pointwise bound implies genuine L² membership
(`app:ch_regular:lem:finite-chain`). -/
theorem memLp_of_support_bound {f : X → ℂ} (hf : AEStronglyMeasurable f μ)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C) (hz : ∀ x, x ∉ s → f x = 0) : MemLp f 2 μ := by
  apply (memLp_indicator_const (μ := μ) 2 hs.nullMeasurableSet (C : ℂ)
    (Or.inr hμs)).of_le hf
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ s
  · simpa [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      using hb x
  · simp [Set.indicator_of_notMem hx, hz x hx]

/-- The L² norm of a bounded function on a finite-measure support
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_toLp_le_of_support_bound {f : X → ℂ} (hf : MemLp f 2 μ)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C) (hz : ∀ x, x ∉ s → f x = 0) :
    ‖hf.toLp f‖ ≤ C * Real.sqrt (μ.real s) := by
  have h : ‖hf.toLp f‖ ≤ ‖indicatorConstLp 2 hs hμs (C : ℂ)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (C : ℂ))]
      with x hx hi
    rw [hx, hi]
    by_cases hxs : x ∈ s
    · simpa [Set.indicator_of_mem hxs, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC] using hb x
    · simp [Set.indicator_of_notMem hxs, hz x hxs]
  convert h using 1
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC, Real.sqrt_eq_rpow]

/-- Cauchy–Schwarz for the actual scalar kernel integral, requiring no
derivatives of the datum (`app:ch_regular:lem:finite-chain`). -/
theorem norm_integral_mul_le_l2 {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have he : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) =
      inner ℝ (hf.norm.toLp (fun x ↦ ‖f x‖)) (hg.norm.toLp (fun x ↦ ‖g x‖)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.norm.coeFn_toLp, hg.norm.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  calc
    ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
    _ ≤ ‖hf.norm.toLp (fun x ↦ ‖f x‖)‖ * ‖hg.norm.toLp (fun x ↦ ‖g x‖)‖ := by
      rw [he]
      exact real_inner_le_norm _ _
    _ = ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
      simp only [Lp.norm_toLp]
      rw [eLpNorm_norm f hf.aestronglyMeasurable, eLpNorm_norm g hg.aestronglyMeasurable]

open RetardedSobolev.Spaces

/-- A pointwise bound on a kernel jet implies its L² membership in the input
variable (`app:ch_regular:lem:finite-chain`). -/
theorem kernelJet_memLp {d e m : ℕ} (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) [IsFiniteMeasureOnCompacts μ]
    (i : JetIndex e m) (p : (Fin e → ℝ) × ℝ)
    (hmeas : AEStronglyMeasurable (kernelJet K i p) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖kernelJet K i p y‖ ≤ C) :
    MemLp (kernelJet K i p) 2 μ :=
  memLp_of_support_bound hmeas K.compact_inputSupport.measurableSet
    K.compact_inputSupport.measure_ne_top hC hb (kernelJet_zero_off_input K i p)

/-- The finite-support kernel-to-jet bound. The only analytic identity assumed
here is differentiation under the integral; it is not an operator estimate.
The regularity construction must supply this identity when applying the theorem
to `kernelIntegral` (`app:ch_regular:eq:chain-tail`). -/
theorem jetMap_bound_of_kernelJet_formula {d e m : ℕ}
    (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : Test d →ₗ[ℂ] Test e)
    (hformula : ∀ (f : Test d) (i : JetIndex e m) p, jet i (T f) p =
      ∫ y, kernelJet K i p y * f.val (y.2, y.1) ∂μ)
    (hmeas : ∀ (i : JetIndex e m) p, AEStronglyMeasurable (kernelJet K i p) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ (i : JetIndex e m) p y, ‖kernelJet K i p y‖ ≤ C)
    (f : Test d) :
    ‖jetMap m ν (T f)‖ ≤
      (C * compactSupportFactor μ ν K.inputSupport (Prod.swap ⁻¹' K.outputSupport)) *
        ‖jetMap 0 μ f‖ := by
  have hcompact : IsCompact (Prod.swap ⁻¹' K.outputSupport) :=
    (Homeomorph.prodComm _ _).isCompact_preimage.mpr K.compact_outputSupport
  have hf : MemLp (fun y : (Fin d → ℝ) × ℝ ↦ f.val (y.2, y.1)) 2 μ := by
    simpa using jet_memLp μ (zeroIndex d 0) f
  have hfbound : ‖hf.toLp (fun y : (Fin d → ℝ) × ℝ ↦ f.val (y.2, y.1))‖ ≤ ‖jetMap 0 μ f‖ := by
    convert norm_le_pi_norm (jetMap 0 μ f) (zeroIndex d 0) using 1
    change ‖hf.toLp _‖ = ‖(jet_memLp μ (zeroIndex d 0) f).toLp _‖
    simp only [Lp.norm_toLp, jet_zeroIndex]
  have hpoint (i : JetIndex e m) (p : (Fin e → ℝ) × ℝ) :
      ‖jet i (T f) p‖ ≤ (C * Real.sqrt (μ.real K.inputSupport)) * ‖jetMap 0 μ f‖ := by
    rw [hformula]
    have hk := kernelJet_memLp K μ i p (hmeas i p) hC (hb i p)
    exact (norm_integral_mul_le_l2 hk hf).trans
      (mul_le_mul (norm_toLp_le_of_support_bound hk
        K.compact_inputSupport.measurableSet K.compact_inputSupport.measure_ne_top
        hC (hb i p) (kernelJet_zero_off_input K i p)) hfbound (norm_nonneg _) (by positivity))
  apply (pi_norm_le_iff_of_nonneg (by unfold compactSupportFactor; positivity)).mpr
  intro i
  have hz (p : (Fin e → ℝ) × ℝ) (hp : p ∉ Prod.swap ⁻¹' K.outputSupport) :
      jet i (T f) p = 0 := by
    rw [hformula]
    simp only [kernelJet_zero_off_output K i p _ hp, zero_mul, integral_zero]
  have h := norm_toLp_le_of_support_bound (jet_memLp ν i (T f))
    hcompact.measurableSet hcompact.measure_ne_top (by positivity) (hpoint i) hz
  change ‖(jet_memLp ν i (T f)).toLp _‖ ≤ _
  convert h using 1
  unfold compactSupportFactor
  ring

/-- Completion of the preceding pointwise-kernel estimate, in the existing
Cartesian Sobolev spaces (`app:ch_regular:eq:chain-tail`). -/
theorem exists_extension_of_kernelJet_formula {d e m : ℕ}
    (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : Test d →ₗ[ℂ] Test e)
    (hformula : ∀ (f : Test d) (i : JetIndex e m) p, jet i (T f) p =
      ∫ y, kernelJet K i p y * f.val (y.2, y.1) ∂μ)
    (hmeas : ∀ (i : JetIndex e m) p, AEStronglyMeasurable (kernelJet K i p) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ (i : JetIndex e m) p y, ‖kernelJet K i p y‖ ≤ C) :
    ∃ A : Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖A‖ ≤ C * compactSupportFactor μ ν K.inputSupport (Prod.swap ⁻¹' K.outputSupport) ∧
      (∀ f, A (ofTest 0 μ f) = ofTest m ν (T f)) ∧
      ∀ B : Sobolev 0 μ →L[ℂ] Sobolev m ν,
        (∀ f, B (ofTest 0 μ f) = ofTest m ν (T f)) → B = A :=
  exists_unique_bounded_extension μ ν T
    (mul_nonneg hC (compactSupportFactor_nonneg _ _ _ _))
    (jetMap_bound_of_kernelJet_formula K μ ν T hformula hmeas hC hb)

end JanetCartan.FiniteChain.Retarded.KernelSobolev
