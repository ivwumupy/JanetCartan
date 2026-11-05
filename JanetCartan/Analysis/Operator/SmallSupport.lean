module

public import JanetCartan.Analysis.Operator.SmallSupport.Cutoff
public import JanetCartan.Analysis.Operator.SmallSupport.Sobolev
public import JanetCartan.Analysis.Operator.SmallSupport.ZeroExtension

/-!
# Small-support contraction from an Lᵖ gain

The cutoff and Hölder steps of `app:ch_regular:thm:exact-correction` in `paper.tex`.
Given a uniform L²(W)-to-Lᵖ(U) bound, `exists_local_cutoffs_norm_lt` constructs
smooth nested cutoffs and an operator on all of L²(W) with norm below any positive
threshold. Use `μ = volume.restrict W` and a measurable `U ⊆ W` for the manuscript.

The residual's analytic bound is an explicit input. The Sobolev helper relates it
to Mathlib's actual whole-space inequality for supplied compact C¹ representatives;
no local Sobolev extension or residual estimate is asserted here. This module does
not prove the Neumann inverse or the rest of the exact-correction theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace JanetCartan.SmallSupport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual localized residual χ₂ R χ₃, extended by zero to the ambient L²
space (`app:ch_regular:thm:exact-correction`). -/
def localizedResidual (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U) (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U)) :
    Lp F 2 μ →L[ℝ] Lp F 2 μ :=
  (bumpL2 hp χ₂).comp
    (((zeroExtend hU).toContinuousLinearMap.comp R).comp (bumpL2 (p := 2) le_rfl χ₃))

/-- The localized residual has the claimed pointwise meaning
(`app:ch_regular:thm:exact-correction`). -/
theorem localizedResidual_coeFn (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U) (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    (f : Lp F 2 μ) :
    localizedResidual hp χ₂ χ₃ hU R f =ᵐ[μ]
      fun y ↦ χ₂ y • U.indicator (R (bumpL2 (p := 2) le_rfl χ₃ f)) y := by
  have h₁ := bumpL2_coeFn hp χ₂
    ((zeroExtend hU) (R (bumpL2 (p := 2) le_rfl χ₃ f)))
  have h₂ := zeroExtend_coeFn hU (R (bumpL2 (p := 2) le_rfl χ₃ f))
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  exact hy₁.trans (congrArg (fun v ↦ χ₂ y • v) hy₂)

/-- The manuscript's quantitative support estimate for a residual whose output
is defined only on `U` (`app:ch_regular:thm:exact-correction`). -/
theorem norm_localizedResidual_le (hp : 2 ≤ p) {x : E} (χ₂ χ₃ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U) (R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U))
    {C : ℝ} (hR : ‖R‖ ≤ C) :
    ‖localizedResidual hp χ₂ χ₃ hU R‖ ≤
      (μ (tsupport (χ₂ : E → ℝ))).toReal ^ (1 / 2 - 1 / (p : ℝ)) * C :=
  norm_localized_le hp χ₂.continuous.aestronglyMeasurable (bump_norm_le_one χ₂)
    (subset_tsupport _) χ₂.hasCompactSupport.measure_lt_top.ne
    ((zeroExtend hU).toContinuousLinearMap.comp R) (bumpL2 (p := 2) le_rfl χ₃)
    ((norm_zeroExtend_comp_le hU R).trans hR) (norm_bumpL2_two_le_one χ₃)

/-- Uniform smooth cutoffs making the local residual small on the entire ambient
L² space (`app:ch_regular:thm:exact-correction`). The bumps are compactly supported,
valued in `[0,1]`, and equal to one on balls of positive radius about `x`.
In particular χ₂ determines a nonempty open core. Choose `0 < θ < 1` to obtain
the contraction used by the Neumann argument. -/
theorem exists_local_cutoffs_norm_lt [Measure.OuterRegular μ] [NullSingletonClass μ]
    (hp : 2 < p) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (C : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : E → ℝ) ⊆ U ∧ tsupport (χ₃ : E → ℝ) ⊆ U ∧
      (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) ∧
      ∀ R : Lp F 2 μ →L[ℝ] Lp F p (μ.restrict U), ‖R‖ ≤ C →
        ‖localizedResidual hp.le χ₂ χ₃ hU.measurableSet R‖ < θ := by
  obtain ⟨χ₂, χ₃, h₂, h₃, hnest, hnorm⟩ :=
    exists_cutoffs_norm_lt (F := F) (μ := μ) hp (hU.mem_nhds hx) C hθ
  exact ⟨χ₂, χ₃, h₂, h₃, hnest, fun R hR ↦
    hnorm ((zeroExtend hU.measurableSet).toContinuousLinearMap.comp R)
      ((norm_zeroExtend_comp_le hU.measurableSet R).trans hR)⟩

end JanetCartan.SmallSupport
