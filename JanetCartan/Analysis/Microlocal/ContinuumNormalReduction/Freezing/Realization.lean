module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization.Amplitude
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.IntegerBounds.Endpoints

/-!
# Bounded scalar Taylor coefficient operators on Euclidean L²

For `app:ch_background:prop:bg-frame`, Step 3, construct the actual bounded
operators from primitive symbol jets and two fixed smooth physical cutoffs.
Their representatives on smooth L² data are the Taylor symbol operators applied
to the source-cutoff datum. No amplitude estimate, bounded Taylor operator, or
freezing decomposition is assumed. The consuming matrix freezing construction
must supply the primitive jets and fixed cutoffs and assemble the final identity.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff NNReal FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp (α := E) ℂ 2

/-- The source-cutoff datum as an actual Schwartz function, for
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingCutoffSchwartz (γ : E → ℝ) (hγ : ContDiff ℝ ∞ γ)
    (hγs : HasCompactSupport γ) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) : 𝓢(E, ℂ) :=
  hγs.smul_right.toSchwartzMap (hγ.smul hu)

/-- Source integration of the literal Taylor amplitude factors through the
Fourier transform of the cutoff datum (`app:ch_background:prop:bg-frame`). -/
theorem sourceAmplitudeTransform_freezingTaylorAmplitude
    (a : E → E → ℂ) (β γ : E → ℝ) (hγ : ContDiff ℝ ∞ γ)
    (hγs : HasCompactSupport γ) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (i : Fin d) (x ξ : E) :
    sourceAmplitudeTransform (fun x y ξ ↦ freezingTaylorAmplitude a β γ i ξ
      (pairedPosition x y)) u x ξ =
      (𝓕 (freezingCutoffSchwartz γ hγ hγs u hu) : 𝓢(E, ℂ)) ξ •
        extendedFreezingTaylorCoefficient a β i x ξ := by
  simp only [freezingTaylorAmplitude_pairedPosition, sourceAmplitudeTransform]
  change 𝓕 (fun y ↦ u y • (γ y • extendedFreezingTaylorCoefficient a β i x ξ)) ξ =
    𝓕 (fun y ↦ γ y • u y) ξ • extendedFreezingTaylorCoefficient a β i x ξ
  have heq : (fun y ↦ u y • (γ y • extendedFreezingTaylorCoefficient a β i x ξ)) =
      (fun y ↦ (γ y • u y) • extendedFreezingTaylorCoefficient a β i x ξ) := by
    funext y
    rw [smul_assoc, smul_comm]
  rw [heq]
  simp only [Real.fourier_eq, Circle.smul_def, smul_smul, integral_smul_const]
  rfl

/-- The source-first integral is the Taylor symbol operator on the cutoff
datum, with both physical cutoffs retained (`app:ch_background:prop:bg-frame`). -/
theorem fullAmplitudeOperator_freezingTaylorAmplitude
    (a : E → E → ℂ) (β γ : E → ℝ) (hγ : ContDiff ℝ ∞ γ)
    (hγs : HasCompactSupport γ) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (i : Fin d) :
    fullAmplitudeOperator (fun x y ξ ↦ freezingTaylorAmplitude a β γ i ξ
      (pairedPosition x y)) u =
      sourceIndependentOperator (extendedFreezingTaylorCoefficient a β i)
        (freezingCutoffSchwartz γ hγ hγs u hu) := by
  funext x
  unfold fullAmplitudeOperator sourceIndependentOperator
  rw [show sourceAmplitudeTransform (fun x y ξ ↦
    freezingTaylorAmplitude a β γ i ξ (pairedPosition x y)) u x =
      (fun ξ ↦ (𝓕 (freezingCutoffSchwartz γ hγ hγs u hu) : 𝓢(E, ℂ)) ξ •
        extendedFreezingTaylorCoefficient a β i x ξ) from
    funext (fun ξ ↦ sourceAmplitudeTransform_freezingTaylorAmplitude a β γ hγ hγs u hu i x ξ)]

section PrimitiveData
variable (hd : 0 < d) (R : ℝ)
  (a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
  (β γ : EuclideanSpace ℝ (Fin d) → ℝ)
  (ha : ContDiff ℝ ∞ (Function.uncurry a))
  (hβ : ContDiff ℝ ∞ β) (hγ : ContDiff ℝ ∞ γ)
  (hβbox : ∀ x, β x ≠ 0 → ∀ j, |x j| ≤ R)
  (hγbox : ∀ y, γ y ≠ 0 → ∀ j, |y j| ≤ R)
  (B G M : ℝ≥0)
  (hb : ∀ k ≤ 2 * (d + 1), ∀ x, ‖iteratedFDeriv ℝ k β x‖ ≤ B)
  (hg : ∀ k ≤ 2 * (d + 1), ∀ y, ‖iteratedFDeriv ℝ k γ y‖ ≤ G)
  (hm : ∀ k ≤ 2 * (d + 1) + 1, ∀ p,
    ‖iteratedFDeriv ℝ k (Function.uncurry a) p‖ ≤ M)

/-- The actual scalar Taylor coefficient operator on Euclidean Lebesgue L²
in `app:ch_background:prop:bg-frame`, Step 3. Its hypotheses are solely
smoothness, fixed physical support boxes, and finite primitive jet budgets. -/
def freezingTaylorL2Operator (i : Fin d) : L² →L[ℂ] L² :=
  twoPositionL2Operator hd R (freezingTaylorAmplitude a β γ i)
    (contDiff_freezingTaylorAmplitude a β γ ha hβ hγ i)
    (supportedInCenteredBox_freezingTaylorAmplitude a β γ R hβbox hγbox i)
    (freezingAmplitudeBudget (d := d) B G M (2 * (d + 1)))
    (hasAmplitudeDerivativeBound_freezingTaylorAmplitude a β γ ha hβ hγ B G M
      (2 * (d + 1)) hb hg hm i)

/-- Uniform operator norm bound for the Taylor coefficients of
`app:ch_background:prop:bg-frame`, independent of the eventual radius `r`. -/
theorem norm_freezingTaylorL2Operator_le (i : Fin d) :
    ‖freezingTaylorL2Operator hd R a β γ ha hβ hγ hβbox hγbox B G M hb hg hm i‖ ≤
      fixedBoxAmplitudeConstant d R *
        freezingAmplitudeBudget (d := d) B G M (2 * (d + 1)) :=
  norm_twoPositionL2Operator_le ..

/-- The all-data zero-order estimate used in `app:ch_background:prop:bg-frame`,
Step 3. This uses the existing Sobolev endpoint of the actual realization. -/
theorem freezingTaylorL2Operator_zero_all_data (i : Fin d) (f : L²) :
    MemFourierSobolev 0
        (freezingTaylorL2Operator hd R a β γ ha hβ hγ hβbox hγbox B G M hb hg hm i f) ∧
      fourierSobolevNorm 0
        (freezingTaylorL2Operator hd R a β γ ha hβ hγ hβbox hγbox B G M hb hg hm i f) ≤
        (fixedBoxAmplitudeConstant d R *
          freezingAmplitudeBudget (d := d) B G M (2 * (d + 1))) * ‖f‖ :=
  twoPositionL2Operator_zero_all_data ..

include ha hβ hγ hb hm in
/-- Primitive order-one symbol jets and the output cutoff bound suffice for
frequency integrability on the cutoff datum (`app:ch_background:prop:bg-frame`). -/
theorem integrable_sourceAmplitudeTransform_freezingTaylorAmplitude
    (hγs : HasCompactSupport γ) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (i : Fin d) (x : E) :
    Integrable (sourceAmplitudeTransform (fun x y ξ ↦
      freezingTaylorAmplitude a β γ i ξ (pairedPosition x y)) u x) := by
  rw [show sourceAmplitudeTransform (fun x y ξ ↦
    freezingTaylorAmplitude a β γ i ξ (pairedPosition x y)) u x =
      (fun ξ ↦ (𝓕 (freezingCutoffSchwartz γ hγ hγs u hu) : 𝓢(E, ℂ)) ξ •
        extendedFreezingTaylorCoefficient a β i x ξ) from
    funext (fun ξ ↦ sourceAmplitudeTransform_freezingTaylorAmplitude a β γ hγ hγs u hu i x ξ)]
  apply integrable_sourceIndependentOperator_symbol _ _ x
    ((contDiff_extendedFreezingTaylorCoefficient a β ha hβ i).continuous.comp
      (continuous_const.prodMk continuous_id)) ((B : ℝ) * M / 2) 0
  intro ξ
  have h := norm_iteratedFDeriv_extendedFreezingTaylorCoefficient_le a β ha hβ i
    (x, ξ) 0 (fun _ ↦ (M : ℝ)) (fun k hk t _ ↦ hm (k + 1) (by omega) _)
  have hb0 := hb 0 (by omega) x
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
    norm_iteratedFDeriv_zero] at h
  simp only [norm_iteratedFDeriv_zero] at hb0
  simp only [pow_zero, show (B : ℝ) * M / 2 * (1 + 1) = B * M by ring]
  exact h.trans (mul_le_mul_of_nonneg_right hb0 M.coe_nonneg)

/-- Identification of the constructed L² operator on every smooth L² datum,
including Schwartz and compact smooth tests (`app:ch_background:prop:bg-frame`).
The integrability premise of the general realization theorem is discharged. -/
theorem freezingTaylorL2Operator_toLp_ae_sourceIndependentOperator
    (hγs : HasCompactSupport γ) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (hu₂ : MemLp u 2) (i : Fin d) :
    freezingTaylorL2Operator hd R a β γ ha hβ hγ hβbox hγbox B G M hb hg hm i
        (hu₂.toLp u) =ᵐ[volume]
      sourceIndependentOperator (extendedFreezingTaylorCoefficient a β i)
        (freezingCutoffSchwartz γ hγ hγs u hu) := by
  rw [← fullAmplitudeOperator_freezingTaylorAmplitude a β γ hγ hγs u hu i]
  exact twoPositionL2Operator_toLp_ae_fullAmplitudeOperator hd R
    (freezingTaylorAmplitude a β γ i) _ _ _ _ u hu₂
    (Filter.Eventually.of_forall (fun x ↦
      integrable_sourceAmplitudeTransform_freezingTaylorAmplitude a β γ ha hβ hγ
        B M hb hm hγs u hu i x))

end PrimitiveData
end JanetCartan.ContinuumNormal
