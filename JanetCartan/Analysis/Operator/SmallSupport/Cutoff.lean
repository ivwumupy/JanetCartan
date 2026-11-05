module

public import JanetCartan.Analysis.Operator.SmallSupport.Holder
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Smooth cutoffs giving a contraction

The cutoff choice in `app:ch_regular:thm:exact-correction` of `paper.tex`.
The core is chosen along with the cutoffs: a prescribed core of positive measure
cannot in general be retained while making the support arbitrarily small.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace JanetCartan.SmallSupport

/-- A positive power of the support measure makes any fixed constant small
(`app:ch_regular:thm:exact-correction`). -/
theorem exists_measure_threshold {p : ℝ≥0} (hp : 2 < p) (C : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ > 0, ∀ m : ℝ, 0 ≤ m → m < δ → m ^ (1 / 2 - 1 / (p : ℝ)) * C < θ := by
  have hc : Continuous (fun m : ℝ ↦ m ^ (1 / 2 - 1 / (p : ℝ)) * C) :=
    (Real.continuous_rpow_const (supportExponent_pos hp).le).mul_const C
  have hzero : (0 : ℝ) ^ (1 / 2 - 1 / (p : ℝ)) * C < θ := by
    rw [Real.zero_rpow (supportExponent_pos hp).ne', zero_mul]
    exact hθ
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.eventually (gt_mem_nhds hzero))
  refine ⟨δ, hδ, fun m hm hmd ↦ hsub ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hm] using hmd

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Smooth bump functions satisfy the unit cutoff bound
(`app:ch_regular:thm:exact-correction`). -/
theorem bump_norm_le_one {x : E} (χ : ContDiffBump x) (y : E) : ‖χ y‖ ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_nonneg χ.nonneg] using χ.le_one (x := y)

variable [Fact (1 ≤ (p : ℝ≥0∞))]

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Smooth output multiplication on Lᵖ, with values in L²
(`app:ch_regular:thm:exact-correction`). -/
def bumpL2 (hp : 2 ≤ p) {x : E} (χ : ContDiffBump x) : Lp F p μ →L[ℝ] Lp F 2 μ :=
  cutoffL2 hp χ.continuous.aestronglyMeasurable (bump_norm_le_one χ)
    (subset_tsupport _) χ.hasCompactSupport.measure_lt_top.ne

/-- The smooth cutoff acts by the stated pointwise formula
(`app:ch_regular:thm:exact-correction`). -/
theorem bumpL2_coeFn (hp : 2 ≤ p) {x : E} (χ : ContDiffBump x) (f : Lp F p μ) :
    bumpL2 hp χ f =ᵐ[μ] fun y ↦ χ y • f y :=
  cutoffL2_coeFn hp _ _ _ _ f

/-- The support controls the smooth cutoff's operator norm
(`app:ch_regular:thm:exact-correction`). -/
theorem norm_bumpL2_le (hp : 2 ≤ p) {x : E} (χ : ContDiffBump x) :
    ‖bumpL2 (F := F) (μ := μ) hp χ‖ ≤
      (μ (tsupport χ)).toReal ^ (1 / 2 - 1 / (p : ℝ)) :=
  norm_cutoffL2_le hp _ _ _ _

/-- The input cutoff is an L² contraction
(`app:ch_regular:thm:exact-correction`). -/
theorem norm_bumpL2_two_le_one {x : E} (χ : ContDiffBump x) :
    ‖bumpL2 (F := F) (μ := μ) (p := 2) le_rfl χ‖ ≤ 1 := by
  simpa using norm_bumpL2_le (F := F) (μ := μ) (p := 2) le_rfl χ

/-- Uniform small-support contraction from an L²-to-Lᵖ bound, the cutoff step of
`app:ch_regular:thm:exact-correction`. Both cutoffs are smooth, compactly supported
in `U`, valued in `[0,1]`, and the inner cutoff is one near `x` (properties of
`ContDiffBump`). The same cutoffs work for every residual with norm at most `C`.
This proves the cutoff step conditional on that analytic bound, not the bound itself. -/
theorem exists_cutoffs_norm_lt [Measure.OuterRegular μ] [NullSingletonClass μ]
    (hp : 2 < p) {U : Set E} {x : E} (hU : U ∈ 𝓝 x) (C : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ χ₂ χ₃ : ContDiffBump x,
      tsupport (χ₂ : E → ℝ) ⊆ U ∧ tsupport (χ₃ : E → ℝ) ⊆ U ∧
      (∀ y ∈ tsupport (χ₂ : E → ℝ), χ₃ y = 1) ∧
      ∀ R : Lp F 2 μ →L[ℝ] Lp F p μ, ‖R‖ ≤ C →
        ‖(bumpL2 hp.le χ₂).comp (R.comp (bumpL2 (p := 2) le_rfl χ₃))‖ < θ := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_measure_threshold hp C hθ
  obtain ⟨V, hxV, hV, hμV⟩ := ({x} : Set E).exists_isOpen_lt_of_lt
    (μ := μ) (ENNReal.ofReal δ) (by simpa using ENNReal.ofReal_pos.mpr hδ)
  have hVx : V ∈ 𝓝 x := hV.mem_nhds (hxV (mem_singleton x))
  obtain ⟨d, hd, hdsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hU hVx)
  let χ₂ : ContDiffBump x := ⟨d / 4, d / 2, by positivity, by linarith⟩
  let χ₃ : ContDiffBump x := ⟨d / 2, d, by positivity, by linarith⟩
  have h₂ : tsupport (χ₂ : E → ℝ) ⊆ closedBall x d := by
    rw [χ₂.tsupport_eq]
    exact closedBall_subset_closedBall (by dsimp [χ₂]; linarith)
  have h₃ : tsupport (χ₃ : E → ℝ) ⊆ closedBall x d := by
    rw [χ₃.tsupport_eq]
  refine ⟨χ₂, χ₃, h₂.trans (hdsub.trans inter_subset_left),
    h₃.trans (hdsub.trans inter_subset_left), ?_, ?_⟩
  · intro y hy
    apply χ₃.one_of_mem_closedBall
    simpa [χ₂.tsupport_eq] using hy
  · intro R hR
    have hμ₂ : μ (tsupport (χ₂ : E → ℝ)) < ENNReal.ofReal δ :=
      (measure_mono (h₂.trans (hdsub.trans inter_subset_right))).trans_lt hμV
    have hm : (μ (tsupport (χ₂ : E → ℝ))).toReal < δ := by
      have := (ENNReal.toReal_lt_toReal hμ₂.ne_top ENNReal.ofReal_ne_top).mpr hμ₂
      simpa [ENNReal.toReal_ofReal hδ.le] using this
    exact (norm_localized_le hp.le χ₂.continuous.aestronglyMeasurable
      (bump_norm_le_one χ₂) (subset_tsupport _) χ₂.hasCompactSupport.measure_lt_top.ne
      R (bumpL2 (p := 2) le_rfl χ₃) hR (norm_bumpL2_two_le_one χ₃)).trans_lt
      (hsmall _ ENNReal.toReal_nonneg hm)

end JanetCartan.SmallSupport
