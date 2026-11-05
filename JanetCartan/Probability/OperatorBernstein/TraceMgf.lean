module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.LiebConcavity
public import JanetCartan.Probability.OperatorBernstein.SingleMgf
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Order
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Integration
public import JanetCartan.Probability.OperatorBernstein.TraceMgf.Iteration

/-!
# Independent-sum trace MGF estimate

Minsker (3.4), used in `app:ch_waves:thm:sampling` of `paper.tex`, follows
from the independent-sum cumulant bound and the deterministic log-MGF comparison.
The final theorem combines these bounds with centering to prove the expected
trace-remainder estimate. The companion integration module exposes variance
positivity and trace-remainder integrability under the same hypotheses.

Matrix integration uses the Frobenius norm, while all probabilistic bounds use
the explicit Euclidean `operatorNorm`. Empty family and matrix index types are
allowed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : ι → Ω → Matrix d d ℂ} {R θ : ℝ}

/-- Summing Minsker's single-matrix log-MGF bound (3.3) gives the deterministic
matrix comparison used in (3.4) (`app:ch_waves:thm:sampling`). -/
theorem sum_log_integral_exp_smul_le_variance
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hθ : 0 ≤ θ) :
    (∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ)) ≤
      (expRemainder (θ * R) / R ^ 2) • variance μ Y := by
  rw [variance, Finset.smul_sum]
  exact Finset.sum_le_sum fun i _ =>
    log_integral_exp_smul_le (hY i) (hH i) (hcenter i) (hbound i) hR hθ

/-- The deterministic last step of Minsker (3.4): trace monotonicity converts the
summed log-MGF estimate into the variance trace bound
(`app:ch_waves:thm:sampling`). Independence is only needed for the preceding
expectation-to-cumulant step. -/
theorem realTrace_exp_sum_log_mgf_sub_one_le_variance
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hθ : 0 ≤ θ) :
    realTrace (NormedSpace.exp (∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ)) - 1) ≤
      realTrace (NormedSpace.exp ((expRemainder (θ * R) / R ^ 2) • variance μ Y) - 1) := by
  have hlogs : (∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ)).IsHermitian :=
    (isSelfAdjoint_sum Finset.univ fun _ _ => IsSelfAdjoint.log).isHermitian
  have hvariance := ((variance_posSemidef hH).smul
    (div_nonneg (expRemainder_nonneg (θ * R)) (sq_nonneg R))).isHermitian
  have h := realTrace_exp_mono hlogs hvariance
    (sum_log_integral_exp_smul_le_variance hY hH hcenter hbound hR hθ)
  simpa only [realTrace, Matrix.trace_sub, Complex.sub_re] using
    sub_le_sub_right h (realTrace (1 : Matrix d d ℂ))

/-- Minsker (3.4), the independent-sum trace-exponential estimate used in
`app:ch_waves:thm:sampling` of `paper.tex`. For independent centered Hermitian
matrices bounded in operator norm by `R`, the expected trace remainder is bounded
by the variance trace exponential. All Jensen, independence, and integrability
requirements follow from the stated hypotheses.

The associated positivity and integrability results are `variance_posSemidef`
and `integrable_realTrace_exp_remainder_matrix_sum`. -/
theorem integral_realTrace_exp_remainder_sum_le_variance
    (hIndep : iIndepFun Y μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (hR : 0 < R) (hθ : 0 < θ) :
    (∫ ω, realTrace
      (NormedSpace.exp (θ • ∑ i, Y i ω) - θ • ∑ i, Y i ω - 1) ∂μ) ≤
      realTrace (NormedSpace.exp ((expRemainder (θ * R) / R ^ 2) • variance μ Y) - 1) := by
  rw [integral_realTrace_exp_remainder_matrix_sum hY hcenter hbound θ]
  have h := integral_realTrace_exp_sum_le_sum_log_mgf
    hIndep hY hH hcenter hbound hR hθ.le
  have hsub :
      (∫ ω, realTrace (NormedSpace.exp (θ • ∑ i, Y i ω)) ∂μ) -
          realTrace (1 : Matrix d d ℂ) ≤
        realTrace (NormedSpace.exp
          (∑ i, CFC.log (∫ ω, NormedSpace.exp (θ • Y i ω) ∂μ)) - 1) := by
    simpa only [realTrace, Matrix.trace_sub, Complex.sub_re] using
      sub_le_sub_right h (realTrace (1 : Matrix d d ℂ))
  exact hsub.trans
    (realTrace_exp_sum_log_mgf_sub_one_le_variance hY hH hcenter hbound hR hθ.le)

end JanetCartan.OperatorBernstein
