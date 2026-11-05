module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.NormalSeries
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Bounded multiplication and Fourier multipliers

The Plancherel and bounded-multiplication inputs to `app:ch_osc:lem:osc-amplitude`.
Mathlib's Euclidean Fourier transform has phase `exp(-2π i x·ξ)`; hence its frequency
variable is the unit-period frequency, and the physical frequency is `2π ξ`, as in
`JanetCartan.Analysis.Fourier.Periodic`. Symbols passed here are functions of that
unit-period frequency. No additional Fourier normalization is introduced.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace JanetCartan.AmplitudeBound

section Multiplication

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Multiplication by a bounded measurable coefficient, used in
`app:ch_osc:lem:osc-amplitude`. -/
def multiplicationOperator (a : Lp ℂ ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ ∞ 2 2 a

/-- The multiplication operator in `app:ch_osc:lem:osc-amplitude` acts pointwise. -/
theorem multiplicationOperator_coeFn (a : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    multiplicationOperator a f =ᵐ[μ] fun x ↦ a x * f x :=
  (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder a f

/-- The elementary `L∞ × L² → L²` estimate used in
`app:ch_osc:lem:osc-amplitude`. -/
theorem norm_multiplicationOperator_le (a : Lp ℂ ∞ μ) :
    ‖multiplicationOperator a‖ ≤ ‖a‖ := by
  calc
    ‖multiplicationOperator a‖ ≤
        ‖(ContinuousLinearMap.lsmul ℂ ℂ (E := ℂ)).holderL μ ∞ 2 2‖ * ‖a‖ :=
      ContinuousLinearMap.le_opNorm _ a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.opNorm_lsmul_le)
      (norm_nonneg _)
    _ = ‖a‖ := one_mul _

/-- The normal bound of `app:ch_osc:eq:two-position-normal-bound` for actual bounded
coefficient functions and a bounded mask, conditional on the physical Fourier
coefficient majorant. The sum has not yet been identified with an integral kernel. -/
theorem norm_normalAmplitudeOperator_multiplication_le {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L R : ι → H →L[ℂ] H) (T : Lp ℂ 2 μ →L[ℂ] H)
    (a : ι → Lp ℂ ∞ μ) (g : Lp ℂ ∞ μ) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c) :
    ‖normalAmplitudeOperator L R T
      (fun i ↦ (multiplicationOperator (a i)).comp (multiplicationOperator g))‖ ≤
      (∑' i, c i) * ‖T‖ ^ 2 * ‖g‖ := by
  apply norm_normalAmplitudeOperator_le L R T _ c ‖g‖ hL hR _ hc
  intro i
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ((norm_multiplicationOperator_le _).trans (ha i))
      (norm_multiplicationOperator_le _) (norm_nonneg _)
      ((norm_nonneg _).trans (ha i)))

end Multiplication

section Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The bounded Fourier multiplier in `app:ch_osc:lem:osc-amplitude`, with symbol
in the unit-period frequency variable (physical frequency `2π ξ`). -/
def fourierMultiplier (a : Lp (α := E) ℂ ∞) :
    Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2 :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((multiplicationOperator a).comp
      (Lp.fourierTransformₗᵢ E ℂ).toLinearIsometry.toContinuousLinearMap)

/-- Plancherel gives the multiplier bound in `app:ch_osc:lem:osc-amplitude`
without any frequency-support restriction. -/
theorem norm_fourierMultiplier_le (a : Lp (α := E) ℂ ∞) :
    ‖fourierMultiplier (E := E) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖(Lp.fourierTransformₗᵢ E ℂ).symm
    (multiplicationOperator a (Lp.fourierTransformₗᵢ E ℂ f))‖ ≤ ‖a‖ * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  calc
    ‖multiplicationOperator a (Lp.fourierTransformₗᵢ E ℂ f)‖ ≤
        ‖multiplicationOperator a‖ * ‖Lp.fourierTransformₗᵢ E ℂ f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖a‖ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (norm_multiplicationOperator_le _) (norm_nonneg _)

/-- The two-position Fourier series estimate in `app:ch_osc:lem:osc-amplitude`
from a summable `L∞` bound on the physical Fourier coefficients. -/
theorem norm_amplitudeOperator_fourierMultiplier_le {ι : Type*}
    (L R : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (a : ι → Lp (α := E) ℂ ∞) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1)
    (ha : ∀ i, ‖a i‖ ≤ c i) (hc : Summable c) :
    ‖amplitudeOperator L R (fun i ↦ fourierMultiplier (a i))‖ ≤ ∑' i, c i :=
  norm_amplitudeOperator_le L R _ c hL hR
    (fun i ↦ (norm_fourierMultiplier_le _).trans (ha i)) hc

/-- Strong convergence of regularized coefficient operators gives the distributional
limit required in `app:ch_osc:lem:osc-amplitude`. This identifies the limit of the
operator series; identifying it with the oscillatory integral is a separate step. -/
theorem tendsto_amplitudeOperator_temperedDistribution {ι α : Type*} {l : Filter α}
    (L R C : ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2)
    (Creg : α → ι → Lp (α := E) ℂ 2 →L[ℂ] Lp (α := E) ℂ 2) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) (hreg : ∀ a i, ‖Creg a i‖ ≤ c i)
    (hlim : ∀ i f, Tendsto (fun a ↦ Creg a i f) l (𝓝 (C i f)))
    (f : Lp (α := E) ℂ 2) :
    Tendsto (fun a ↦ Lp.toTemperedDistribution (amplitudeOperator L R (Creg a) f)) l
      (𝓝 (Lp.toTemperedDistribution (amplitudeOperator L R C f))) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.continuousAt.tendsto.comp
    (tendsto_amplitudeOperator_apply L R C Creg c hL hR hC hc hreg hlim f)

end Fourier

end JanetCartan.AmplitudeBound
