module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.SingleMgf

/-!
# Integrability and centering for finite matrix sums

Analytic bookkeeping for Minsker (3.4), used in `app:ch_waves:thm:sampling`
of `paper.tex`. All integrals use the Frobenius norm, and all probabilistic
bounds use the explicit Euclidean operator norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d : Type*} [Fintype d]

/-- The real trace as a continuous real-linear map, for exchanging trace and
expectation in `app:ch_waves:thm:sampling` (Minsker (3.4)). -/
def realTraceCLM : Matrix d d ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap d ℝ ℂ).toContinuousLinearMap

/-- Evaluation of the trace map used in Minsker (3.4)
(`app:ch_waves:thm:sampling`). -/
@[simp] theorem realTraceCLM_apply (A : Matrix d d ℂ) : realTraceCLM A = realTrace A := rfl

/-- Continuity of real trace for `app:ch_waves:thm:sampling`, Minsker (3.4). -/
theorem continuous_realTrace : Continuous (realTrace (d := d)) := realTraceCLM.continuous

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The trace of an integrable matrix is integrable
(`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem integrable_realTrace {X : Ω → Matrix d d ℂ} (hX : Integrable X μ) :
    Integrable (fun ω => realTrace (X ω)) μ := realTraceCLM.integrable_comp hX

/-- Real trace commutes with matrix expectation in Minsker (3.4)
(`app:ch_waves:thm:sampling`). -/
theorem integral_realTrace {X : Ω → Matrix d d ℂ} (hX : Integrable X μ) :
    (∫ ω, realTrace (X ω) ∂μ) = realTrace (∫ ω, X ω ∂μ) :=
  realTraceCLM.integral_comp_comm hX

variable [DecidableEq d] [Fintype ι] {Y : ι → Ω → Matrix d d ℂ} {R : ℝ}

/-- A finite sum inherits an almost-sure operator bound
(`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem ae_operatorNorm_sum_le (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) :
    ∀ᵐ ω ∂μ, operatorNorm (∑ i, Y i ω) ≤ ∑ _i : ι, R := by
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  unfold operatorNorm at *
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hω i)

omit [Fintype d] [DecidableEq d] in
/-- Measurability of the sum in Minsker (3.4)
(`app:ch_waves:thm:sampling`). -/
theorem aestronglyMeasurable_matrix_sum (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable (fun ω => ∑ i, Y i ω) μ := by
  exact Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => hY i)

/-- The variance in Minsker (3.4) is positive semidefinite, without needing
independence or centering (`app:ch_waves:thm:sampling`). -/
theorem variance_posSemidef (hH : ∀ i, ∀ᵐ ω ∂μ, (Y i ω).IsHermitian) :
    (variance μ Y).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun i _ => integral_mul_self_nonneg (hH i)

variable [IsProbabilityMeasure μ]

/-- Integrability of a finite bounded matrix sum
(`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem integrable_matrix_sum (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) :
    Integrable (fun ω => ∑ i, Y i ω) μ :=
  integrable_of_operatorNorm_le (aestronglyMeasurable_matrix_sum hY)
    (ae_operatorNorm_sum_le hbound)

/-- A finite sum of centered bounded matrices is centered
(`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem integral_matrix_sum_eq_zero (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) :
    (∫ ω, ∑ i, Y i ω ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => integrable_of_operatorNorm_le (hY i) (hbound i))]
  simp [hcenter]

/-- Integrability of the trace exponential with a deterministic offset, as used
in the independence iteration for Minsker (3.4) (`app:ch_waves:thm:sampling`). -/
theorem integrable_realTrace_exp_add_matrix_sum
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R)
    (H : Matrix d d ℂ) (θ : ℝ) :
    Integrable (fun ω => realTrace (NormedSpace.exp (H + θ • ∑ i, Y i ω))) μ := by
  apply integrable_realTrace
  apply integrable_continuous_of_operatorNorm_le
    (f := fun A : Matrix d d ℂ => NormedSpace.exp (H + θ • A))
    (aestronglyMeasurable_matrix_sum hY) (ae_operatorNorm_sum_le hbound)
  exact NormedSpace.exp_continuous.comp (continuous_const.add (continuous_const_smul θ))

/-- The scalar trace remainder in Minsker (3.4) is integrable under the boundedness
hypotheses of `app:ch_waves:thm:sampling`. -/
theorem integrable_realTrace_exp_remainder_matrix_sum
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) (θ : ℝ) :
    Integrable (fun ω => realTrace
      (NormedSpace.exp (θ • ∑ i, Y i ω) - θ • ∑ i, Y i ω - 1)) μ := by
  apply integrable_realTrace
  exact ((integrable_exp_smul_of_operatorNorm_le (aestronglyMeasurable_matrix_sum hY)
    (ae_operatorNorm_sum_le hbound) θ).sub ((integrable_matrix_sum hY hbound).smul θ)).sub
      (integrable_const _)

/-- Centering removes the linear term from the expected trace remainder
(`app:ch_waves:thm:sampling`, Minsker (3.4)). -/
theorem integral_realTrace_exp_remainder_matrix_sum
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hcenter : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, operatorNorm (Y i ω) ≤ R) (θ : ℝ) :
    (∫ ω, realTrace (NormedSpace.exp (θ • ∑ i, Y i ω) - θ • ∑ i, Y i ω - 1) ∂μ) =
      (∫ ω, realTrace (NormedSpace.exp (θ • ∑ i, Y i ω)) ∂μ) - realTrace (1 : Matrix d d ℂ) := by
  have hs : Integrable (fun ω => θ • ∑ i, Y i ω) μ :=
    (integrable_matrix_sum hY hbound).smul θ
  have he := integrable_exp_smul_of_operatorNorm_le (aestronglyMeasurable_matrix_sum hY)
    (ae_operatorNorm_sum_le hbound) θ
  rw [integral_realTrace (X := fun ω => NormedSpace.exp (θ • ∑ i, Y i ω) -
    θ • ∑ i, Y i ω - 1) ((he.sub hs).sub (integrable_const (1 : Matrix d d ℂ))),
    integral_sub (f := fun ω => NormedSpace.exp (θ • ∑ i, Y i ω) - θ • ∑ i, Y i ω)
      (g := fun _ => (1 : Matrix d d ℂ)) (he.sub hs) (integrable_const _),
    integral_sub he hs,
    integral_smul, integral_matrix_sum_eq_zero hY hcenter hbound,
    smul_zero, sub_zero, integral_const, probReal_univ, one_smul, integral_realTrace he]
  simp [realTrace]

end JanetCartan.OperatorBernstein
