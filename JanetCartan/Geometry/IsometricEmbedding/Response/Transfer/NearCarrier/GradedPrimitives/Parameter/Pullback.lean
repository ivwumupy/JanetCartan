module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Parameter.Coefficient
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.CarrierShift

/-!
# Parameter coefficient pullback retaining both physical positions

The primitive coefficients of `app:ch_response:eq:direct-envelope-profile`
live on `(x, ε, c)`. The amplitude calculus lives on `(x, y, ε, c)`.
The projection between these spaces is a contraction, so pulling back a
coefficient preserves every joint jet bound, including mixed derivatives.
The consumer is the parameter primitive assembly in `GradedPrimitives.Parameter`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.GradedPrimitives

/-- The joint coefficient projection from both physical positions in
`app:ch_response:eq:direct-envelope-profile`. -/
def parameterAmplitudeProjection (n p : ℕ) :
    ParameterAmplitudePoint n (Euclidean p) →L[ℝ] ParameterCoefficientSpace n p :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
      (ContinuousLinearMap.snd ℝ _ _))

/-- The coefficient projection retains `x`, `ε`, and `c` in their literal
order (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterAmplitudeProjection_apply {n p : ℕ}
    (q : ParameterAmplitudePoint n (Euclidean p)) :
    parameterAmplitudeProjection n p q = (q.1.1, q.1.2.2, q.2) := rfl

/-- The amplitude-to-coefficient projection costs no derivative constant
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_parameterAmplitudeProjection_le (n p : ℕ) :
    ‖parameterAmplitudeProjection n p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖(q.1.1, q.1.2.2, q.2)‖ ≤ 1 * ‖q‖
  simp only [one_mul, Prod.norm_def]
  exact max_le
    ((norm_fst_le q.1).trans (norm_fst_le q))
    (max_le ((norm_snd_le q.1.2).trans ((norm_snd_le q.1).trans (norm_fst_le q)))
      (norm_snd_le q))

/-- The reverse kernel has its phase position in the second physical slot.
This projection preserves that literal order in
`app:ch_response:thm:response-literal-transfer`. -/
def reverseParameterAmplitudeProjection (n p : ℕ) :
    ParameterAmplitudePoint n (Euclidean p) →L[ℝ] ParameterCoefficientSpace n p :=
  ((ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
    (((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
      (ContinuousLinearMap.snd ℝ _ _))

/-- Evaluation of the reverse projection in the physical order `(y,x,ε,c)`
of `app:ch_response:thm:response-literal-transfer`. -/
theorem reverseParameterAmplitudeProjection_apply {n p : ℕ}
    (q : ParameterAmplitudePoint n (Euclidean p)) :
    reverseParameterAmplitudeProjection n p q = (q.1.2.1, q.1.2.2, q.2) := rfl

/-- The reverse projection also incurs no jet loss in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_reverseParameterAmplitudeProjection_le (n p : ℕ) :
    ‖reverseParameterAmplitudeProjection n p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖(q.1.2.1, q.1.2.2, q.2)‖ ≤ 1 * ‖q‖
  simp only [one_mul, Prod.norm_def]
  exact max_le
    ((norm_fst_le q.1.2).trans ((norm_snd_le q.1).trans (norm_fst_le q)))
    (max_le ((norm_snd_le q.1.2).trans ((norm_snd_le q.1).trans (norm_fst_le q)))
      (norm_snd_le q))

variable {n p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ParameterCoefficientSpace n p → F}
  {X Y V : Set (Euclidean n)} {C : Set (Euclidean p)}

/-- Smooth coefficient pullback to the full amplitude variables in
`app:ch_response:eq:direct-envelope-profile`. The second position is retained
as an independent variable. -/
theorem parameterAmplitude_pullback_contDiffOn
    (hf : ContDiffOn ℝ ∞ f (X ×ˢ V ×ˢ C)) :
    ContDiffOn ℝ ∞ (f ∘ parameterAmplitudeProjection n p) ((X ×ˢ Y ×ˢ V) ×ˢ C) :=
  hf.comp (parameterAmplitudeProjection n p).contDiff.contDiffOn
    (fun _ hq ↦ ⟨hq.1.1, hq.1.2.2, hq.2⟩)

/-- A contraction pullback preserves the full joint derivative operator
norm. This is used for both `C` and `-C B⁻¹` in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_parameterAmplitude_pullback_le
    (hX : IsOpen X) (hV : IsOpen V) (hC : IsOpen C)
    (hf : ContDiffOn ℝ ∞ f (X ×ˢ V ×ˢ C))
    {q : ParameterAmplitudePoint n (Euclidean p)} (hq : q ∈ (X ×ˢ Y ×ˢ V) ×ˢ C) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ parameterAmplitudeProjection n p) q‖ ≤
      ‖iteratedFDeriv ℝ k f (q.1.1, q.1.2.2, q.2)‖ := by
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (parameterAmplitudeProjection n p) (hX.prod (hV.prod hC)) hf
    ⟨hq.1.1, hq.1.2.2, hq.2⟩ k).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (norm_parameterAmplitudeProjection_le n p)))

/-- Smoothness after the reverse projection, retaining the original kernel
order of both physical positions (`app:ch_response:eq:direct-envelope-profile`). -/
theorem reverseParameterAmplitude_pullback_contDiffOn
    (hf : ContDiffOn ℝ ∞ f (X ×ˢ V ×ˢ C)) :
    ContDiffOn ℝ ∞ (f ∘ reverseParameterAmplitudeProjection n p) ((Y ×ˢ X ×ˢ V) ×ˢ C) :=
  hf.comp (reverseParameterAmplitudeProjection n p).contDiff.contDiffOn
    (fun _ hq ↦ ⟨hq.1.2.1, hq.1.2.2, hq.2⟩)

/-- The literal reverse coefficient is pulled back from the second physical
position without increasing any joint jet norm
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_reverseParameterAmplitude_pullback_le
    (hX : IsOpen X) (hV : IsOpen V) (hC : IsOpen C)
    (hf : ContDiffOn ℝ ∞ f (X ×ˢ V ×ˢ C))
    {q : ParameterAmplitudePoint n (Euclidean p)} (hq : q ∈ (Y ×ˢ X ×ˢ V) ×ˢ C) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ reverseParameterAmplitudeProjection n p) q‖ ≤
      ‖iteratedFDeriv ℝ k f (q.1.2.1, q.1.2.2, q.2)‖ := by
  exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (reverseParameterAmplitudeProjection n p) (hX.prod (hV.prod hC)) hf
    ⟨hq.1.2.1, hq.1.2.2, hq.2⟩ k).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (norm_reverseParameterAmplitudeProjection_le n p)))

end JanetCartan.ResponseTransfer.GradedPrimitives
