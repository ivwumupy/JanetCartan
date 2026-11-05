module

public import JanetCartan.Analysis.Operator.Retarded.TimeIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Support

/-! # Finite-time L² estimates

Cauchy–Schwarz estimates used in `app:ch_osc:prop:osc-retarded-tube`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.Retarded

/-- Cauchy–Schwarz against the constant function, as used in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem integral_norm_sq_le_measure_mul {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (f := fun _ : α ↦ (1 : ℝ)) (g := fun x ↦ ‖f x‖)
    (μ := μ) (by simpa using (memLp_const (1 : ℝ) : MemLp _ 2 μ))
    (by simpa using hf.norm)
  simp only [norm_one, one_mul, integral_const, smul_eq_mul,
    Real.norm_eq_abs, abs_norm, Real.rpow_two, one_pow, mul_one, ← Real.sqrt_eq_rpow] at h
  have hpos : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg (fun x ↦ norm_nonneg _)
  have hsq := sq_le_sq₀ hpos (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr h
  simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg),
    Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖f x‖))] using hsq

/-- A bounded cutoff estimate for any time mask, used in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem norm_integral_mask_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f w : α → ℂ) (p : α → Prop) [DecidablePred p] {C : ℝ}
    (hf : Integrable f μ) (hC : 0 ≤ C) (hw : ∀ᵐ s ∂μ, ‖w s‖ ≤ C) :
    ‖∫ s, if p s then w s * f s else 0 ∂μ‖ ≤ C * ∫ s, ‖f s‖ ∂μ := by
  calc
    _ ≤ ∫ s, C * ‖f s‖ ∂μ := norm_integral_le_of_norm_le (hf.norm.const_mul C) (by
      filter_upwards [hw] with s hs
      split_ifs
      · simpa only [norm_mul] using mul_le_mul_of_nonneg_right hs (norm_nonneg (f s))
      · simpa only [norm_zero] using mul_nonneg hC (norm_nonneg (f s)))
    _ = _ := integral_const_mul _ _

/-- The squared integral estimate from a uniform time-fiber bound, used in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem integral_sq_le_of_uniform_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f g : α → ℂ) (hf : MemLp f 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C * ∫ s, ‖f s‖ ∂μ) :
    (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ C ^ 2 * (μ.real univ) ^ 2 * ∫ s, ‖f s‖ ^ 2 ∂μ := by
  have hsq : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ (C * ∫ s, ‖f s‖ ∂μ) ^ 2 := by
    filter_upwards [hg] with x hx
    exact sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (integral_nonneg (fun s ↦ norm_nonneg _))) |>.mpr hx
  calc
    _ ≤ ∫ _ : α, (C * ∫ s, ‖f s‖ ∂μ) ^ 2 ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
        (integrable_const _) hsq
    _ = μ.real univ * (C ^ 2 * (∫ s, ‖f s‖ ∂μ) ^ 2) := by
      rw [integral_const, smul_eq_mul, mul_pow]
    _ ≤ μ.real univ * (C ^ 2 * (μ.real univ * ∫ s, ‖f s‖ ^ 2 ∂μ)) := by
      gcongr
      exact integral_norm_sq_le_measure_mul μ f hf
    _ = _ := by ring

/-- Integrating fiber L² estimates gives the product-measure estimate used in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem memLp_two_prod_of_fiber_estimate {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (f g : A × B → ℂ) (hf : MemLp f 2 (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, MemLp (fun y ↦ g (x, y)) 2 ν ∧
      (∫ y, ‖g (x, y)‖ ^ 2 ∂ν) ≤ C * ∫ y, ‖f (x, y)‖ ^ 2 ∂ν) :
    MemLp g 2 (μ.prod ν) ∧
      (∫ z, ‖g z‖ ^ 2 ∂μ.prod ν) ≤ C * ∫ z, ‖f z‖ ^ 2 ∂μ.prod ν := by
  have hfi : Integrable (fun z ↦ ‖f z‖ ^ 2) (μ.prod ν) := hf.integrable_norm_pow (by norm_num)
  have hgi_meas : AEStronglyMeasurable (fun z ↦ ‖g z‖ ^ 2) (μ.prod ν) := hg.norm.pow 2
  have houter : Integrable (fun x ↦ ∫ y, ‖g (x, y)‖ ^ 2 ∂ν) μ := by
    apply (hfi.integral_prod_left.const_mul C).mono hgi_meas.integral_prod_right'
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y ↦ sq_nonneg ‖g (x, y)‖)),
      abs_of_nonneg (mul_nonneg hC (integral_nonneg (fun y ↦ sq_nonneg ‖f (x, y)‖)))] using hx.2
  have hgi : Integrable (fun z ↦ ‖g z‖ ^ 2) (μ.prod ν) := by
    apply (integrable_prod_iff hgi_meas).2
    constructor
    · filter_upwards [hbound] with x hx
      exact hx.1.integrable_norm_pow (by norm_num)
    · simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using houter
  refine ⟨(memLp_two_iff_integrable_sq_norm hg).2 hgi, ?_⟩
  rw [integral_prod _ hgi, integral_prod _ hfi, ← integral_const_mul]
  exact integral_mono_ae houter (hfi.integral_prod_left.const_mul C) (hbound.mono (fun x hx ↦ hx.2))

/-- Bounded cutoff multiplication preserves integrability, as used for the
Fubini calculation in `app:ch_osc:eq:retarded-literal-adjoint`. -/
theorem integrable_mul_cutoff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w f : α → ℂ) (hw : AEStronglyMeasurable w μ) (hf : Integrable f μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) : Integrable (fun x ↦ w x * f x) μ := by
  apply (hf.norm.const_mul C).mono' (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- An L² function on a product has L² time fibers almost everywhere;
used in `app:ch_osc:prop:osc-retarded-tube`. -/
theorem memLp_two_fiber_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {f : A × B → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ f (x, y)) 2 ν := by
  have hfi : Integrable (fun z ↦ ‖f z‖ ^ 2) (μ.prod ν) := hf.integrable_norm_pow (by norm_num)
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hfi.prod_right_ae] with x hfm hfi
  exact (memLp_two_iff_integrable_sq_norm hfm).2 hfi

/-- Compactly supported continuous cutoffs have a nonnegative uniform bound,
as required by `app:ch_osc:setup:osc-retarded`. -/
theorem exists_cutoff_bound {X : Type*} [TopologicalSpace X] (χ : X → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |χ x| ≤ C := by
  obtain ⟨C, hC⟩ := (hs.isCompact_range hc).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  exact (hC (χ x) (mem_range_self x)).trans (le_max_left _ _)

end JanetCartan.Retarded
