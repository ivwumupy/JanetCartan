module

public import JanetCartan.Probability.OperatorBernstein.TraceMgf
public import JanetCartan.Probability.OperatorBernstein.TailConversion

/-!
# Finite-dimensional operator Bernstein

The finite-dimensional Minsker Bernstein bound used in
`app:ch_waves:thm:sampling` of `paper.tex`, equations (3.6)–(3.9) of the cited
source. The independent-sum trace estimate supplies both signed moments and
their integrability; the tail conversion then gives the constant 14 bound.

The variance parameter is any positive upper bound, including when the actual
variance is zero. Matrix integration retains the Frobenius norm, and the event
uses the explicit Euclidean operator norm. Empty index types are allowed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : ι → Ω → Matrix d d ℂ} {R v τ t : ℝ}

/-- Finite-dimensional Minsker Bernstein inequality, as used in
`app:ch_waves:thm:sampling` of `paper.tex`. Independent centered Hermitian
matrices bounded by `R` satisfy the two-sided operator-norm tail bound with
constant 14, whenever `t² ≥ v + Rt/3`. The positive variance upper bound `v`
need not equal the norm of the variance, so zero variance is included. -/
theorem operatorBernstein
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hv : 0 < v) (hVv : operatorNorm (variance μ Y) ≤ v)
    (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ.real {ω | t < operatorNorm (∑ i, Y i ω)} ≤
      tailBound R v (realTrace (variance μ Y)) t := by
  have hnegY : ∀ i, AEStronglyMeasurable (fun ω => -Y i ω) μ :=
    fun i => (hY i).neg
  have hnegH : ∀ i, ∀ᵐ ω ∂μ, (-Y i ω).IsHermitian := by
    intro i
    filter_upwards [hH i] with ω hω using hω.neg
  have hnegcenter : ∀ i, ∫ ω, -Y i ω ∂μ = 0 := by
    intro i
    rw [integral_neg, hcenter i, neg_zero]
  have hnegbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (-Y i ω) ≤ R := by
    simpa only [operatorNorm, map_neg, norm_neg] using hbound
  have hnegIndep : iIndepFun (fun i ω => -Y i ω) μ :=
    hIndep.comp (fun _ A => -A) (fun _ => measurable_neg)
  have hnegvariance : variance μ (fun i ω => -Y i ω) = variance μ Y := by
    simp only [variance, neg_mul_neg]
  apply operatorBernstein_of_trace_moments (aestronglyMeasurable_matrix_sum hY)
    _ (variance_posSemidef hH) hR hv hVv _ _ ht hthreshold
  · filter_upwards [ae_all_iff.mpr hH] with ω hω
    exact (isSelfAdjoint_sum Finset.univ fun i _ => (hω i).isSelfAdjoint).isHermitian
  · intro θ _ ε hε
    rcases hε with rfl | rfl
    · simpa only [one_smul] using
        integrable_realTrace_exp_remainder_matrix_sum hY hbound θ
    · simpa only [neg_one_smul, Finset.sum_neg_distrib] using
        integrable_realTrace_exp_remainder_matrix_sum hnegY hnegbound θ
  · intro θ hθ ε hε
    rcases hε with rfl | rfl
    · simpa only [one_smul] using
        integral_realTrace_exp_remainder_sum_le_variance hIndep hY hH hcenter hbound hR hθ
    · simpa only [neg_one_smul, Finset.sum_neg_distrib, hnegvariance] using
        integral_realTrace_exp_remainder_sum_le_variance
          hnegIndep hnegY hnegH hnegcenter hnegbound hR hθ

/-- The finite-dimensional Bernstein bound with the trace upper bound `τ`
used uniformly over prefixes in `app:ch_waves:thm:sampling`. All analytic
moment and integrability requirements follow from the stated hypotheses. -/
theorem operatorBernstein_of_trace_le
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hv : 0 < v) (hVv : operatorNorm (variance μ Y) ≤ v)
    (htrace : realTrace (variance μ Y) ≤ τ)
    (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ.real {ω | t < operatorNorm (∑ i, Y i ω)} ≤ tailBound R v τ t :=
  (operatorBernstein hIndep hY hH hcenter hbound hR hv hVv ht hthreshold).trans
    (tailBound_mono_trace hv htrace)

end JanetCartan.OperatorBernstein
