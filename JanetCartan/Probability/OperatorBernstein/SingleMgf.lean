module

public import JanetCartan.Probability.OperatorBernstein.Basic
public import JanetCartan.Probability.OperatorBernstein.SingleMgf.Integration
public import JanetCartan.Probability.OperatorBernstein.SingleMgf.MatrixOrder

/-!
# The single-matrix moment generating function

Minsker Lemma 3.1, equation (3.3), used in `app:ch_waves:thm:sampling` of `paper.tex`.
The matrix integral uses the Frobenius norm, while `operatorNorm` is explicitly
the norm of the action on Euclidean space.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder ComplexOrder

namespace JanetCartan.OperatorBernstein

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Matrix d d ℂ} {R : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The second moment in Minsker (3.3) is positive semidefinite
(`app:ch_waves:thm:sampling`). -/
theorem integral_mul_self_nonneg (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    0 ≤ ∫ ω, X ω * X ω ∂μ := by
  apply integral_nonneg_of_ae
  filter_upwards [hH] with ω hω
  exact hω.isSelfAdjoint.mul_self_nonneg

/-- The MGF of a bounded centered Hermitian random matrix is above the identity
(Minsker (3.3); `app:ch_waves:thm:sampling`). -/
theorem one_le_integral_exp_smul (hX : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (θ : ℝ) :
    1 ≤ ∫ ω, NormedSpace.exp (θ • X ω) ∂μ := by
  have hi := integrable_of_operatorNorm_le hX hbound
  have he := integrable_exp_smul_of_operatorNorm_le hX hbound θ
  have h := integral_mono_ae ((integrable_const (1 : Matrix d d ℂ)).add (hi.smul θ)) he
    (show ∀ᵐ ω ∂μ, 1 + θ • X ω ≤ NormedSpace.exp (θ • X ω) from by
      filter_upwards [hH] with ω hω
      exact one_add_le_exp (hω.smul (show IsSelfAdjoint θ from isSelfAdjoint_iff.mpr (star_trivial θ))))
  change (∫ ω, 1 + θ • X ω ∂μ) ≤ _ at h
  have hleft : (∫ ω, 1 + θ • X ω ∂μ) = (1 : Matrix d d ℂ) := by
    calc
      _ = (∫ _ : Ω, (1 : Matrix d d ℂ) ∂μ) + ∫ ω, θ • X ω ∂μ :=
        integral_add (integrable_const _) (hi.smul θ)
      _ = 1 + θ • ∫ ω, X ω ∂μ := by rw [integral_smul]; simp
      _ = 1 := by rw [hcenter, smul_zero, add_zero]
  exact hleft ▸ h

/-- Positive definiteness of the MGF in Minsker (3.3), with integrability derived
from the stated bound (`app:ch_waves:thm:sampling`). -/
theorem posDef_integral_exp_smul (hX : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (θ : ℝ) :
    (∫ ω, NormedSpace.exp (θ • X ω) ∂μ).PosDef :=
  posDef_of_one_le (one_le_integral_exp_smul hX hH hcenter hbound θ)

/-- The integrated quadratic bound from Minsker Appendix A, with centering removing
the linear term (`app:ch_waves:thm:sampling`). -/
theorem integral_exp_smul_le_one_add_variance (hX : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (hR : 0 < R)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ ω, NormedSpace.exp (θ • X ω) ∂μ) ≤
      1 + (expRemainder (θ * R) / R ^ 2) • (∫ ω, X ω * X ω ∂μ) := by
  let c := expRemainder (θ * R) / R ^ 2
  have hi := integrable_of_operatorNorm_le hX hbound
  have h2 := integrable_mul_self_of_operatorNorm_le hX hbound
  have he := integrable_exp_smul_of_operatorNorm_le hX hbound θ
  have hl := (integrable_const (1 : Matrix d d ℂ)).add (hi.smul θ)
  have h := integral_mono_ae he (hl.add (h2.smul c))
    (show ∀ᵐ ω ∂μ, NormedSpace.exp (θ • X ω) ≤
      1 + θ • X ω + c • (X ω * X ω) from by
      filter_upwards [hH, hbound] with ω hω hb
      exact exp_smul_le_quadratic hω hR hθ hb)
  have hlinear : (∫ ω, 1 + θ • X ω ∂μ) = (1 : Matrix d d ℂ) := by
    calc
      _ = (∫ _ : Ω, (1 : Matrix d d ℂ) ∂μ) + ∫ ω, θ • X ω ∂μ :=
        integral_add (integrable_const _) (hi.smul θ)
      _ = 1 + θ • ∫ ω, X ω ∂μ := by rw [integral_smul]; simp
      _ = 1 := by rw [hcenter, smul_zero, add_zero]
  have hpoly : (∫ ω, 1 + θ • X ω + c • (X ω * X ω) ∂μ) =
      1 + c • (∫ ω, X ω * X ω ∂μ) := by
    calc
      _ = (∫ ω, 1 + θ • X ω ∂μ) + ∫ ω, c • (X ω * X ω) ∂μ :=
        integral_add hl (h2.smul c)
      _ = _ := by rw [hlinear, integral_smul]
  exact h.trans_eq hpoly

/-- Minsker Lemma 3.1, equation (3.3): the log-MGF of a bounded centered Hermitian
random matrix is bounded by its second moment. All integrability follows from the
operator bound (`app:ch_waves:thm:sampling`). -/
theorem log_integral_exp_smul_le (hX : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (hR : 0 < R)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    CFC.log (∫ ω, NormedSpace.exp (θ • X ω) ∂μ) ≤
      (expRemainder (θ * R) / R ^ 2) • (∫ ω, X ω * X ω ∂μ) := by
  refine (log_le_sub_one (posDef_integral_exp_smul hX hH hcenter hbound θ)).trans ?_
  rw [sub_le_iff_le_add]
  simpa only [add_comm] using
    integral_exp_smul_le_one_add_variance hX hH hcenter hbound hR hθ

/-- Positive definiteness and the single-matrix log-MGF estimate of Minsker (3.3),
used by `app:ch_waves:thm:sampling`. Integration is in the Frobenius norm and the
almost-sure bound is the Euclidean operator norm. -/
theorem single_matrix_log_mgf (hX : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, operatorNorm (X ω) ≤ R) (hR : 0 < R)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ ω, NormedSpace.exp (θ • X ω) ∂μ).PosDef ∧
    CFC.log (∫ ω, NormedSpace.exp (θ • X ω) ∂μ) ≤
      (expRemainder (θ * R) / R ^ 2) • (∫ ω, X ω * X ω ∂μ) :=
  ⟨posDef_integral_exp_smul hX hH hcenter hbound θ,
    log_integral_exp_smul_le hX hH hcenter hbound hR hθ⟩

end JanetCartan.OperatorBernstein
