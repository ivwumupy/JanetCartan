module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.TraceExponential
public import JanetCartan.Probability.OperatorBernstein.ScalarOptimization
public import JanetCartan.Probability.OperatorBernstein.TailConversion.Spectral

/-!
# Conditional conversion of trace moments to operator Bernstein tails

This proves the finite-dimensional tail conversion in
`app:ch_waves:thm:sampling` of `paper.tex`, using Minsker (3.2), (3.6)–(3.9).
The hypotheses are precisely integrability and the two signed trace-moment
bounds. Establishing these hypotheses for independent centered sums is a
separate task. The spectral step uses event inclusion, and the variance upper
bound is positive even when the variance matrix itself is zero.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]

/-- Markov's inequality after the two-sided spectral event inclusion, as needed
in `app:ch_waves:thm:sampling`, Minsker (3.2). The Hermitian condition and event
inclusion are only required almost everywhere. -/
theorem measure_operatorNorm_gt_le_traceRemainders {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Matrix d d ℂ} (hS : ∀ᵐ ω ∂μ, (S ω).IsHermitian)
    {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hplus : Integrable (fun ω ↦ traceRemainder θ (S ω)) μ)
    (hminus : Integrable (fun ω ↦ traceRemainder θ (-S ω)) μ) :
    μ.real {ω | t < operatorNorm (S ω)} ≤
      ((∫ ω, traceRemainder θ (S ω) ∂μ) +
        ∫ ω, traceRemainder θ (-S ω) ∂μ) / expRemainder (θ * t) := by
  have hp : 0 < expRemainder (θ * t) := expRemainder_pos (mul_pos hθ ht)
  have hnonneg : 0 ≤ᵐ[μ] (fun ω ↦ traceRemainder θ (S ω) + traceRemainder θ (-S ω)) := by
    filter_upwards [hS] with ω hω
    exact add_nonneg (traceRemainder_nonneg hω θ) (traceRemainder_nonneg hω.neg θ)
  have hincl : {ω | t < operatorNorm (S ω)} ≤ᵐ[μ]
      {ω | expRemainder (θ * t) ≤ traceRemainder θ (S ω) + traceRemainder θ (-S ω)} := by
    filter_upwards [hS] with ω hω
    exact fun hωt ↦ expRemainder_le_two_traceRemainders hω hθ.le ht.le hωt
  have hmeasure : μ.real {ω | t < operatorNorm (S ω)} ≤
      μ.real {ω | expRemainder (θ * t) ≤
        traceRemainder θ (S ω) + traceRemainder θ (-S ω)} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hincl)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg (hplus.add hminus)
    (expRemainder (θ * t))
  rw [integral_add hplus hminus] at hmarkov
  apply (le_div_iff₀ hp).2
  calc
    _ = expRemainder (θ * t) * μ.real {ω | t < operatorNorm (S ω)} := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hmeasure hp.le).trans hmarkov

/-- Conditional finite-dimensional operator Bernstein bound for
`app:ch_waves:thm:sampling`, Minsker (3.2), (3.6)–(3.9).

The only moment inputs are integrability of the signed trace remainders and
bounds by the trace of `exp ((φ(θR)/R²) • V) - 1`. In particular, neither a
probability estimate nor an effective-rank estimate is assumed. The positive
upper bound `v` permits `V = 0` without dividing by `operatorNorm V`. -/
theorem operatorBernstein_of_trace_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → Matrix d d ℂ} (_hS : AEStronglyMeasurable S μ)
    (hHermitian : ∀ᵐ ω ∂μ, (S ω).IsHermitian)
    {V : Matrix d d ℂ} (hV : V.PosSemidef) {R v : ℝ}
    (hR : 0 < R) (hv : 0 < v) (hVv : operatorNorm V ≤ v)
    (hIntegrable : ∀ θ : ℝ, 0 < θ → ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      Integrable (fun ω ↦ realTrace
        (NormedSpace.exp (θ • (ε • S ω)) - θ • (ε • S ω) - 1)) μ)
    (hMoment : ∀ θ : ℝ, 0 < θ → ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      (∫ ω, realTrace (NormedSpace.exp (θ • (ε • S ω)) - θ • (ε • S ω) - 1) ∂μ) ≤
        realTrace (NormedSpace.exp ((expRemainder (θ * R) / R ^ 2) • V) - 1))
    {t : ℝ} (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ.real {ω | t < operatorNorm (S ω)} ≤ tailBound R v (realTrace V) t := by
  let θ := bernsteinParameter R v t
  have hθ : 0 < θ := bernsteinParameter_pos hR.le hv ht
  have hplus : Integrable (fun ω ↦ traceRemainder θ (S ω)) μ := by
    simpa only [one_smul, traceRemainder] using hIntegrable θ hθ 1 (Or.inl rfl)
  have hminus : Integrable (fun ω ↦ traceRemainder θ (-S ω)) μ := by
    simpa only [neg_one_smul, traceRemainder] using hIntegrable θ hθ (-1) (Or.inr rfl)
  have hmplus : (∫ ω, traceRemainder θ (S ω) ∂μ) ≤
      realTrace (NormedSpace.exp ((expRemainder (θ * R) / R ^ 2) • V) - 1) := by
    simpa only [one_smul, traceRemainder] using hMoment θ hθ 1 (Or.inl rfl)
  have hmminus : (∫ ω, traceRemainder θ (-S ω) ∂μ) ≤
      realTrace (NormedSpace.exp ((expRemainder (θ * R) / R ^ 2) • V) - 1) := by
    simpa only [neg_one_smul, traceRemainder] using hMoment θ hθ (-1) (Or.inr rfl)
  have hvariance := realTrace_exp_sub_one_le_exp hV hv hVv
    (expRemainder (θ * R) / R ^ 2)
  calc
    _ ≤ ((∫ ω, traceRemainder θ (S ω) ∂μ) +
          ∫ ω, traceRemainder θ (-S ω) ∂μ) / expRemainder (θ * t) :=
      measure_operatorNorm_gt_le_traceRemainders hHermitian hθ ht hplus hminus
    _ ≤ 2 * (realTrace V / v * Real.exp (expRemainder (θ * R) / R ^ 2 * v)) /
        expRemainder (θ * t) := by
      apply div_le_div_of_nonneg_right _ (expRemainder_nonneg _)
      linarith [hmplus.trans hvariance, hmminus.trans hvariance]
    _ ≤ _ := two_trace_ratio_le_tailBound hR hv (realTrace_nonneg hV) ht hthreshold

end JanetCartan.OperatorBernstein
