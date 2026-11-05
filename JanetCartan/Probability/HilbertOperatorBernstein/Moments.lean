module

public import JanetCartan.Probability.HilbertOperatorBernstein.MatrixRepresentation

/-!
# Second moments for Hilbert-space Bernstein

Scalar and operator integrals needed by the finite-compression application in
`app:ch_waves:thm:sampling`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped InnerProductSpace

namespace JanetCartan.HilbertOperatorBernstein

variable {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → E →L[ℂ] E} {R : ℝ}

omit [CompleteSpace E] in
/-- The bounded operator square is Bochner integrable
(`app:ch_waves:thm:sampling`, variance of a compression). -/
theorem integrable_square (hY : AEStronglyMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) : Integrable (fun ω => Y ω * Y ω) μ := by
  apply Integrable.of_bound (hY.mul hY) (R * R)
  filter_upwards [hbound] with ω hω
  exact (norm_mul_le _ _).trans (mul_self_le_mul_self (norm_nonneg _) hω)

omit [CompleteSpace E] in
/-- Bounded random operators have integrable scalar second moments
(`app:ch_waves:thm:sampling`, compression variance domination). -/
theorem integrable_norm_sq_apply (hY : AEStronglyMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) (x : E) :
    Integrable (fun ω => ‖Y ω x‖ ^ 2) μ := by
  apply Integrable.of_bound ((hY.apply_continuousLinearMap x).norm.pow 2) ((R * ‖x‖) ^ 2)
  filter_upwards [hbound] with ω hω
  change ‖‖Y ω x‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (Y ω).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

/-- The quadratic form of the integrated square is its scalar second moment
(`app:ch_waves:thm:sampling`). -/
theorem re_inner_integral_square
    (hY : AEStronglyMeasurable Y μ) (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R)
    (hsa : ∀ᵐ ω ∂μ, IsSelfAdjoint (Y ω)) (x : E) :
    Complex.re ⟪x, (∫ ω, Y ω * Y ω ∂μ) x⟫_ℂ = ∫ ω, ‖Y ω x‖ ^ 2 ∂μ := by
  have hi := integrable_square hY hbound
  have ha : Integrable (fun ω => (Y ω * Y ω) x) μ :=
    hi.apply_continuousLinearMap x
  rw [ContinuousLinearMap.integral_apply hi, ← integral_inner ha]
  have hr := Complex.reCLM.integral_comp_comm ((innerSL ℂ x).integrable_comp ha)
  change (∫ ω, (⟪x, (Y ω * Y ω) x⟫_ℂ).re ∂μ) =
    (∫ ω, ⟪x, (Y ω * Y ω) x⟫_ℂ ∂μ).re at hr
  rw [← hr]
  apply integral_congr_ae
  filter_upwards [hsa] with ω hω
  exact OperatorCompression.re_inner_square (Y ω) hω x

/-- A positive quadratic-form bound controls the norm of a self-adjoint operator
(`app:ch_waves:thm:sampling`, variance upper parameter). -/
theorem norm_le_of_quadratic_bounds (T : E →L[ℂ] E) (hsa : IsSelfAdjoint T)
    {v : ℝ} (hv : 0 ≤ v)
    (hpos : ∀ x, 0 ≤ Complex.re ⟪x, T x⟫_ℂ)
    (hupper : ∀ x, Complex.re ⟪x, T x⟫_ℂ ≤ v * ‖x‖ ^ 2) : ‖T‖ ≤ v := by
  rw [T.norm_eq_iSup_rayleighQuotient hsa.isSymmetric]
  apply ciSup_le
  intro x
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, RCLike.re_to_complex]
  rw [abs_of_nonneg (div_nonneg (hpos x) (sq_nonneg _))]
  by_cases hx : x = 0
  · simp [hx, hv]
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr (hupper x)

end JanetCartan.HilbertOperatorBernstein
