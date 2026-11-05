module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers

/-!
# Finite amplitude regularizations

The finite physical Fourier sums and compact frequency cutoffs used in
`app:ch_osc:lem:osc-amplitude`. The norm bound is uniform in both truncations.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Restriction of a coefficient to a measurable frequency set in
`app:ch_osc:lem:osc-amplitude`. -/
def truncateSymbol (s : Set X) (hs : MeasurableSet s) (a : Lp ℂ ∞ μ) : Lp ℂ ∞ μ :=
  ((Lp.memLp a).indicator hs.nullMeasurableSet).toLp (s.indicator a)

/-- The truncated coefficient in `app:ch_osc:lem:osc-amplitude` is the actual
indicator cutoff, up to the almost-everywhere equality used by `Lp`. -/
theorem truncateSymbol_coeFn (s : Set X) (hs : MeasurableSet s) (a : Lp ℂ ∞ μ) :
    truncateSymbol s hs a =ᵐ[μ] s.indicator a :=
  MemLp.coeFn_toLp _

/-- Frequency truncation does not increase the coefficient bound in
`app:ch_osc:lem:osc-amplitude`. -/
theorem norm_truncateSymbol_le (s : Set X) (hs : MeasurableSet s) (a : Lp ℂ ∞ μ) :
    ‖truncateSymbol s hs a‖ ≤ ‖a‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [truncateSymbol_coeFn s hs a] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Compact closed-ball cutoff of a Fourier coefficient, as used in
`app:ch_osc:lem:osc-amplitude`. Radii are in the unit-period frequency variable. -/
def compactFrequencySymbol (ρ : ℝ) (a : Lp (α := E) ℂ ∞) : Lp (α := E) ℂ ∞ :=
  truncateSymbol (Metric.closedBall 0 ρ) measurableSet_closedBall a

/-- The compact regularization in `app:ch_osc:lem:osc-amplitude` vanishes almost
everywhere outside the stated frequency ball. -/
theorem compactFrequencySymbol_eq_zero (ρ : ℝ) (a : Lp (α := E) ℂ ∞) :
    ∀ᵐ x, ρ < ‖x‖ → compactFrequencySymbol ρ a x = 0 := by
  filter_upwards [truncateSymbol_coeFn (Metric.closedBall 0 ρ) measurableSet_closedBall a]
    with x hx
  intro h
  rw [compactFrequencySymbol, hx, Set.indicator_of_notMem]
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h

/-- Simultaneous finite physical Fourier sum and compact frequency regularization
for `app:ch_osc:lem:osc-amplitude`. -/
def regularizedAmplitudeOperator {ι : Type*}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (s : Finset ι) (ρ : ℝ) :
    Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  finiteAmplitudeOperator L R (fun i ↦ fourierMultiplier (compactFrequencySymbol ρ (a i))) s

/-- The finite-regularization estimate in `app:ch_osc:lem:osc-amplitude` is
independent of the number of physical modes and the frequency cutoff radius. -/
theorem norm_regularizedAmplitudeOperator_le {ι : Type*}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c) (s : Finset ι) (ρ : ℝ) :
    ‖regularizedAmplitudeOperator (E := E) L R a s ρ‖ ≤ ∑' i, c i :=
  norm_finiteAmplitudeOperator_le L R _ c hL hR
    (fun i ↦ (norm_fourierMultiplier_le _).trans
      ((norm_truncateSymbol_le _ _ _).trans (ha i))) hc s

end JanetCartan.AmplitudeBound
