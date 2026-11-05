module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Scalar

/-!
# Fixed support bounds for compact kernel operators

Quantitative estimates used for parameter differentiation in
`app:ch_osc:prop:osc-normal`. Neither ambient measure need be finite.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.NormalComparison

/-- Cauchy–Schwarz on a finite measure set, with the indicator norm left explicit
for the fixed support estimate in `app:ch_osc:prop:osc-normal`. -/
theorem integral_indicator_norm_le_L2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} (hB : MeasurableSet B) (hμB : μ B ≠ ∞)
    (h : Lp ℂ 2 μ) :
    (∫ u, B.indicator (fun u ↦ ‖h u‖) u ∂μ) ≤
      ‖indicatorConstLp 2 hB hμB (1 : ℝ)‖ * ‖h‖ := by
  let v : Lp ℝ 2 μ := (Lp.memLp h).norm.toLp (fun u ↦ ‖h u‖)
  have hv : ‖v‖ = ‖h‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable h), Lp.norm_def]
  have heq : (∫ u, B.indicator (fun u ↦ ‖h u‖) u ∂μ) =
      inner ℝ (indicatorConstLp 2 hB hμB (1 : ℝ)) v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hμB) (c := (1 : ℝ)),
      (Lp.memLp h).norm.coeFn_toLp] with u hu hv
    rw [hu, hv]
    by_cases hb : u ∈ B <;> simp [hb]
  rw [heq]
  simpa only [hv] using real_inner_le_norm (indicatorConstLp 2 hB hμB (1 : ℝ)) v

variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- A uniform kernel bound on fixed compact spatial supports gives an explicit
operator norm bound, used in Step 2 of `app:ch_osc:prop:osc-normal`. -/
theorem norm_compactKernelOperator_le_fixedSupport
    {μ : Measure U} {ν : Measure E}
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [SFinite μ] [SFinite ν]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    {A : Set E} {B : Set U} (hA : IsCompact A) (hB : IsCompact B)
    (hsupp : Function.support (Function.uncurry t) ⊆ A ×ˢ B)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x u, ‖t x u‖ ≤ C) :
    ‖compactKernelOperator (μ := μ) (ν := ν) ht hs‖ ≤
      C * ‖indicatorConstLp (μ := ν) 2 hA.measurableSet hA.measure_lt_top.ne (1 : ℝ)‖ *
        ‖indicatorConstLp (μ := μ) 2 hB.measurableSet hB.measure_lt_top.ne (1 : ℝ)‖ := by
  let a := indicatorConstLp (μ := ν) 2 hA.measurableSet hA.measure_lt_top.ne (1 : ℝ)
  let b := indicatorConstLp (μ := μ) 2 hB.measurableSet hB.measure_lt_top.ne (1 : ℝ)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  have hbi : Integrable (B.indicator (fun u ↦ ‖h u‖)) μ :=
    by
      have hh : IntegrableOn (fun u ↦ ‖h u‖) B μ :=
        (((Lp.memLp h).locallyIntegrable (by norm_num)).integrableOn_isCompact hB).norm
      exact hh.integrable_indicator hB.measurableSet
  have hi (x : E) : ‖∫ u, t x u * h u ∂μ‖ ≤ C * ‖b‖ * ‖h‖ := by
    calc
      ‖∫ u, t x u * h u ∂μ‖ ≤ ∫ u, C * B.indicator (fun u ↦ ‖h u‖) u ∂μ := by
        apply norm_integral_le_of_norm_le (hbi.const_mul C)
        exact Eventually.of_forall fun u ↦ by
          by_cases hu : u ∈ B
          · simpa [hu, norm_mul] using
              mul_le_mul_of_nonneg_right (hbound x u) (norm_nonneg (h u))
          · have hz : t x u = 0 := by
              by_contra hn
              exact hu (hsupp (show (x, u) ∈ Function.support (Function.uncurry t) from hn)).2
            simp [hz, hu]
      _ = C * ∫ u, B.indicator (fun u ↦ ‖h u‖) u ∂μ := integral_const_mul _ _
      _ ≤ C * (‖b‖ * ‖h‖) := mul_le_mul_of_nonneg_left
        (integral_indicator_norm_le_L2 hB.measurableSet hB.measure_lt_top.ne h) hC
      _ = _ := by ring
  have ho : ‖compactKernelOperator (μ := μ) (ν := ν) ht hs h‖ ≤
      (C * ‖b‖ * ‖h‖) * ‖a‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [compactKernelOperator_ae_integral (ν := ν) ht hs h,
      indicatorConstLp_coeFn (p := 2) (hs := hA.measurableSet)
        (hμs := hA.measure_lt_top.ne) (c := (1 : ℝ))] with x hx ha
    change ‖compactKernelOperator ht hs h x‖ ≤ _ * ‖a x‖
    rw [hx, ha]
    by_cases hxa : x ∈ A
    · simpa [hxa] using hi x
    · have hz : ∀ u, t x u = 0 := by
        intro u
        by_contra hn
        exact hxa (hsupp (show (x, u) ∈ Function.support (Function.uncurry t) from hn)).1
      simp [hz, hxa]
  calc
    ‖compactKernelOperator ht hs h‖ ≤ (C * ‖b‖ * ‖h‖) * ‖a‖ := ho
    _ = _ := by ring

end JanetCartan.NormalComparison
