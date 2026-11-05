module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Regularization
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Removing compact frequency cutoffs

Strong convergence of the actual compact frequency regularizations in
`app:ch_osc:lem:osc-amplitude`. The physical coefficient bounds remain inputs;
no coefficient convergence hypothesis is needed for these cutoffs.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.AmplitudeBound

variable {X α : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter α} [l.IsCountablyGenerated]

/-- Exhausting measurable cutoffs converge in `L²`, the dominated-convergence
step in `app:ch_osc:lem:osc-amplitude`. -/
theorem tendsto_indicator_L2 (s : α → Set X) (hs : ∀ j, MeasurableSet (s j))
    (hexhaust : ∀ᵐ x ∂μ, ∀ᶠ j in l, x ∈ s j) (f : Lp ℂ 2 μ) :
    Tendsto (fun j ↦ ((Lp.memLp f).indicator (hs j).nullMeasurableSet).toLp
      ((s j).indicator f)) l (𝓝 f) := by
  have hmeas (j : α) := ((Lp.memLp f).aestronglyMeasurable.indicator (hs j)).sub
    (Lp.memLp f).aestronglyMeasurable
  have hconv : Tendsto (fun j ↦ ∫⁻ x, ‖(s j).indicator f x - f x‖ₑ ^ (2 : ℝ) ∂μ)
      l (𝓝 0) := by
    simpa only [lintegral_zero, Pi.sub_apply] using
      (tendsto_lintegral_filter_of_dominated_convergence'
        (fun x ↦ ‖f x‖ₑ ^ (2 : ℝ))
        (Eventually.of_forall fun j ↦ (hmeas j).enorm.pow_const (2 : ℝ))
        (Eventually.of_forall fun j ↦ Eventually.of_forall fun x ↦ by
          by_cases hx : x ∈ s j <;> simp [hx])
        (by simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp f).eLpNorm_lt_top).ne)
        (hexhaust.mono fun x hx ↦ tendsto_nhds_of_eventually_eq
          (hx.mono fun j hj ↦ by simp [hj])) :
        Tendsto _ l (𝓝 (∫⁻ _ : X, (0 : ℝ≥0∞) ∂μ)))
  conv_rhs => rw [← Lp.toLp_coeFn f (Lp.memLp f)]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hmeas _)]
  simpa [Function.comp_def] using
    (ENNReal.continuous_rpow_const (y := 1 / 2)).continuousAt.tendsto.comp hconv

/-- Frequency truncation of a multiplication operator is actual restriction of
its output, as used in `app:ch_osc:lem:osc-amplitude`. -/
theorem multiplicationOperator_truncateSymbol (s : Set X) (hs : MeasurableSet s)
    (a : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    multiplicationOperator (truncateSymbol s hs a) f =
      ((Lp.memLp (multiplicationOperator a f)).indicator hs.nullMeasurableSet).toLp
        (s.indicator (multiplicationOperator a f)) := by
  apply Lp.ext
  filter_upwards [multiplicationOperator_coeFn (truncateSymbol s hs a) f,
    truncateSymbol_coeFn s hs a, multiplicationOperator_coeFn a f,
    MemLp.coeFn_toLp ((Lp.memLp (multiplicationOperator a f)).indicator hs.nullMeasurableSet)]
    with x h1 h2 h3 h4
  rw [h1, h2, h4]
  by_cases hx : x ∈ s <;> simp [hx, h3]

/-- Strong convergence of multiplication operators under exhausting frequency
cutoffs in `app:ch_osc:lem:osc-amplitude`. -/
theorem tendsto_multiplicationOperator_truncateSymbol (s : α → Set X)
    (hs : ∀ j, MeasurableSet (s j)) (hexhaust : ∀ᵐ x ∂μ, ∀ᶠ j in l, x ∈ s j)
    (a : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    Tendsto (fun j ↦ multiplicationOperator (truncateSymbol (s j) (hs j) a) f)
      l (𝓝 (multiplicationOperator a f)) := by
  simp_rw [multiplicationOperator_truncateSymbol]
  exact tendsto_indicator_L2 s hs hexhaust _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Plancherel removes the compact frequency cutoffs in
`app:ch_osc:lem:osc-amplitude`, for every `L²` input and every bounded symbol. -/
theorem tendsto_fourierMultiplier_compactFrequencySymbol
    (a : Lp (α := E) ℂ ∞) (f : Lp (α := E) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦ fourierMultiplier (compactFrequencySymbol ρ a) f) atTop
      (𝓝 (fourierMultiplier a f)) := by
  apply (Lp.fourierTransformₗᵢ E ℂ).symm.continuous.continuousAt.tendsto.comp
  apply tendsto_multiplicationOperator_truncateSymbol
  exact Eventually.of_forall fun x ↦ by
    simpa only [Metric.mem_closedBall, dist_zero_right] using eventually_ge_atTop ‖x‖

/-- Removing the compact frequency cutoff in the full physical Fourier series
of `app:ch_osc:lem:osc-amplitude`. Summable coefficient bounds are the only
analytic input. -/
theorem tendsto_amplitudeOperator_compactFrequencySymbol {ι : Type*}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c) (f : Lp (α := E) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦ amplitudeOperator L R
      (fun i ↦ fourierMultiplier (compactFrequencySymbol ρ (a i))) f) atTop
      (𝓝 (amplitudeOperator L R (fun i ↦ fourierMultiplier (a i)) f)) :=
  tendsto_amplitudeOperator_apply L R _ _ c hL hR
    (fun i ↦ (norm_fourierMultiplier_le _).trans (ha i)) hc
    (fun _ i ↦ (norm_fourierMultiplier_le _).trans
      ((norm_truncateSymbol_le _ _ _).trans (ha i)))
    (fun i g ↦ tendsto_fourierMultiplier_compactFrequencySymbol (a i) g) f

/-- Simultaneous removal of the finite physical sum and compact frequency cutoff
in `app:ch_osc:lem:osc-amplitude`, along any exhaustive family of truncations. -/
theorem tendsto_regularizedAmplitudeOperator {ι β : Type*} {m : Filter β}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c)
    (s : β → Finset ι) (ρ : β → ℝ)
    (hs : ∀ i, ∀ᶠ j in m, i ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := E) ℂ 2) :
    Tendsto (fun j ↦ regularizedAmplitudeOperator L R a (s j) (ρ j) f) m
      (𝓝 (amplitudeOperator L R (fun i ↦ fourierMultiplier (a i)) f)) :=
  tendsto_finiteAmplitudeOperator_apply L R _ _ s c hL hR
    (fun i ↦ (norm_fourierMultiplier_le _).trans (ha i)) hc
    (fun _ i ↦ (norm_fourierMultiplier_le _).trans
      ((norm_truncateSymbol_le _ _ _).trans (ha i)))
    (fun i g ↦ (tendsto_fourierMultiplier_compactFrequencySymbol (a i) g).comp hρ) hs f

/-- The finite regularizations of `app:ch_osc:lem:osc-amplitude` converge as
tempered distributions. This is the distribution associated to the operator series;
identifying the regularizations with integral kernels remains a separate obligation. -/
theorem tendsto_regularizedAmplitudeOperator_temperedDistribution {ι β : Type*} {m : Filter β}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c)
    (s : β → Finset ι) (ρ : β → ℝ)
    (hs : ∀ i, ∀ᶠ j in m, i ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := E) ℂ 2) :
    Tendsto (fun j ↦ Lp.toTemperedDistribution
      (regularizedAmplitudeOperator L R a (s j) (ρ j) f)) m
      (𝓝 (Lp.toTemperedDistribution
        (amplitudeOperator L R (fun i ↦ fourierMultiplier (a i)) f))) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.continuousAt.tendsto.comp
    (tendsto_regularizedAmplitudeOperator L R a c hL hR ha hc s ρ hs hρ f)

end JanetCartan.AmplitudeBound
