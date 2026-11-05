module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability of bounded random matrices

Analytic prerequisites for Minsker (3.3), used by `app:ch_waves:thm:sampling`.
All Bochner integrals use the Frobenius norm; bounds use the Euclidean operator norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → Matrix d d ℂ} {R : ℝ}

omit [IsFiniteMeasure μ] in
/-- The operator-norm bound in Minsker (3.3) gives a Frobenius-norm bound
(`app:ch_waves:thm:sampling`). -/
theorem exists_ae_frobenius_bound_of_operatorNorm_le
    (hR : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) :
    ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖X ω‖ ≤ C := by
  let e := (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  refine ⟨‖e.symm.toContinuousLinearMap‖ * R, ?_⟩
  filter_upwards [hR] with ω hω
  calc
    ‖X ω‖ = ‖e.symm (e (X ω))‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (X ω)‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * R :=
      mul_le_mul_of_nonneg_left hω (ContinuousLinearMap.opNorm_nonneg _)

/-- Every continuous matrix function of an essentially operator-bounded random matrix
is Bochner integrable on a finite measure space (Minsker (3.3),
`app:ch_waves:thm:sampling`). -/
theorem integrable_continuous_of_operatorNorm_le
    (hX : AEStronglyMeasurable X μ)
    (hR : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R)
    {f : Matrix d d ℂ → Matrix d d ℂ} (hf : Continuous f) :
    Integrable (fun ω => f (X ω)) μ := by
  obtain ⟨C, hC⟩ := exists_ae_frobenius_bound_of_operatorNorm_le hR
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Matrix d d ℂ) C).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound (hf.comp_aestronglyMeasurable hX) B ?_
  filter_upwards [hC] with ω hω
  exact hB _ (by simpa using hω)

/-- Integrability of the centered matrix in Minsker (3.3)
(`app:ch_waves:thm:sampling`). -/
theorem integrable_of_operatorNorm_le (hX : AEStronglyMeasurable X μ)
    (hR : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) : Integrable X μ :=
  integrable_continuous_of_operatorNorm_le hX hR continuous_id

/-- Integrability of the second moment in Minsker (3.3)
(`app:ch_waves:thm:sampling`). -/
theorem integrable_mul_self_of_operatorNorm_le (hX : AEStronglyMeasurable X μ)
    (hR : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) :
    Integrable (fun ω => X ω * X ω) μ :=
  integrable_continuous_of_operatorNorm_le hX hR (continuous_id.mul continuous_id)

/-- Integrability of the matrix exponential in Minsker (3.3)
(`app:ch_waves:thm:sampling`). -/
theorem integrable_exp_smul_of_operatorNorm_le (hX : AEStronglyMeasurable X μ)
    (hR : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (θ : ℝ) :
    Integrable (fun ω => NormedSpace.exp (θ • X ω)) μ :=
  integrable_continuous_of_operatorNorm_le hX hR (NormedSpace.exp_continuous.comp (continuous_const_smul θ))

end JanetCartan.OperatorBernstein
