module

public import JanetCartan.Analysis.Operator.SmallSupport.Holder

/-!
# Zero extension in Lᵖ

The zero extension of the localized operator in `app:ch_regular:thm:exact-correction`
requires only Lᵖ theory. This is not a Sobolev extension theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace JanetCartan.SmallSupport

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Set α}

/-- Zero extension from a measurable domain preserves the Lᵖ norm
(`app:ch_regular:thm:exact-correction`). This construction has no Sobolev claim. -/
def zeroExtend (hU : MeasurableSet U) : Lp F p (μ.restrict U) →ₗᵢ[ℝ] Lp F p μ := by
  let mem (f : Lp F p (μ.restrict U)) : MemLp (U.indicator (fun x ↦ f x)) p μ :=
    (memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr (Lp.memLp f)
  refine
    { toFun := fun f ↦ (mem f).toLp _
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq hU).mp (Lp.coeFn_add f g)
    filter_upwards [MemLp.coeFn_toLp (mem (f + g)), hi,
      MemLp.coeFn_toLp (mem f), MemLp.coeFn_toLp (mem g),
      Lp.coeFn_add ((mem f).toLp _) ((mem g).toLp _)] with x h₁ h₂ h₃ h₄ h₅
    by_cases hx : x ∈ U <;> simp_all [Set.indicator]
  · intro c f
    apply Lp.ext
    have hi := (ae_eq_restrict_iff_indicator_ae_eq hU).mp (Lp.coeFn_smul c f)
    filter_upwards [MemLp.coeFn_toLp (mem (c • f)), hi,
      MemLp.coeFn_toLp (mem f), Lp.coeFn_smul c ((mem f).toLp _)] with x h₁ h₂ h₃ h₄
    by_cases hx : x ∈ U <;> simp_all [Set.indicator]
  · intro f
    change ‖(mem f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hU.nullMeasurableSet,
      Lp.norm_def]

/-- Pointwise meaning of Lᵖ zero extension
(`app:ch_regular:thm:exact-correction`). -/
theorem zeroExtend_coeFn (hU : MeasurableSet U) (f : Lp F p (μ.restrict U)) :
    zeroExtend hU f =ᵐ[μ] U.indicator (fun x ↦ f x) :=
  MemLp.coeFn_toLp ((memLp_indicator_iff_restrict hU.nullMeasurableSet).mpr (Lp.memLp f))

/-- Extending the output of a local residual by zero does not increase its norm
(`app:ch_regular:thm:exact-correction`). -/
theorem norm_zeroExtend_comp_le (hU : MeasurableSet U)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : H →L[ℝ] Lp F p (μ.restrict U)) :
    ‖(zeroExtend hU).toContinuousLinearMap.comp R‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  simpa using R.le_opNorm f

end JanetCartan.SmallSupport
