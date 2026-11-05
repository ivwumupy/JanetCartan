module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Small-support localization

The Hölder step in `app:ch_regular:thm:exact-correction` of `paper.tex`.
The residual's L²-to-Lᵖ estimate is an explicit analytic input, not established here.
The measure is arbitrary, so the results also apply to restricted domain measures.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace JanetCartan
namespace SmallSupport

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure α} {p : ℝ≥0}

/-- The positive support exponent in `app:ch_regular:thm:exact-correction`. -/
theorem supportExponent_pos (hp : 2 < p) : 0 < 1 / 2 - 1 / (p : ℝ) := by
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  exact sub_pos.mpr (one_div_lt_one_div_of_lt (by norm_num) hp')

/-- The nonnegative support exponent, including the L² endpoint
(`app:ch_regular:thm:exact-correction`). -/
theorem supportExponent_nonneg (hp : 2 ≤ p) : 0 ≤ 1 / 2 - 1 / (p : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hp')

/-- Hölder on the output support, as used in `app:ch_regular:thm:exact-correction`. -/
theorem eLpNorm_cutoff_le (hp : 2 ≤ p) {χ : α → ℝ} {g : α → F} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hg : AEStronglyMeasurable g μ)
    (hbound : ∀ x, ‖χ x‖ ≤ 1) (hsupport : Function.support χ ⊆ s) :
    eLpNorm (fun x ↦ χ x • g x) 2 μ ≤
      (μ s) ^ (1 / 2 - 1 / (p : ℝ)) * eLpNorm g p μ := by
  have hm : AEStronglyMeasurable (fun x ↦ χ x • g x) μ := hχ.smul hg
  have hs : Function.support (fun x ↦ χ x • g x) ⊆ s := by
    intro x hx
    apply hsupport
    contrapose! hx
    simp_all [Function.mem_support]
  calc
    eLpNorm (fun x ↦ χ x • g x) 2 μ =
        eLpNorm (fun x ↦ χ x • g x) 2 (μ.restrict s) :=
      (eLpNorm_restrict_eq_of_support_subset hm hs).symm
    _ ≤ eLpNorm (fun x ↦ χ x • g x) p (μ.restrict s) *
        (μ s) ^ (1 / 2 - 1 / (p : ℝ)) := by
      simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (show (2 : ℝ≥0∞) ≤ p by exact_mod_cast hp) hm.restrict
    _ ≤ eLpNorm g p (μ.restrict s) * (μ s) ^ (1 / 2 - 1 / (p : ℝ)) := by
      gcongr
      apply eLpNorm_mono_ae hm.restrict
      exact Eventually.of_forall fun x ↦ by
        simpa only [norm_smul, one_mul] using
          mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (g x))
    _ ≤ eLpNorm g p μ * (μ s) ^ (1 / 2 - 1 / (p : ℝ)) :=
      mul_le_mul_left (eLpNorm_restrict_le g p μ s) _
    _ = _ := mul_comm _ _

/-- A bounded cutoff on a finite support maps Lᵖ to L²
(`app:ch_regular:thm:exact-correction`). -/
theorem memLp_cutoff (hp : 2 ≤ p) {χ : α → ℝ} {g : α → F} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hg : MemLp g p μ)
    (hbound : ∀ x, ‖χ x‖ ≤ 1) (hsupport : Function.support χ ⊆ s)
    (hs : μ s ≠ ∞) : MemLp (fun x ↦ χ x • g x) 2 μ := by
  refine lt_of_le_of_lt
    (eLpNorm_cutoff_le hp hχ hg.aestronglyMeasurable hbound hsupport) ?_
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (supportExponent_nonneg hp) hs) hg.eLpNorm_lt_top

variable [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The bounded linear output cutoff Lᵖ → L² from
`app:ch_regular:thm:exact-correction`. -/
def cutoffL2 (hp : 2 ≤ p) {χ : α → ℝ} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hsupport : Function.support χ ⊆ s) (hs : μ s ≠ ∞) :
    Lp F p μ →L[ℝ] Lp F 2 μ := by
  let T : Lp F p μ →ₗ[ℝ] Lp F 2 μ :=
    { toFun := fun f ↦ (memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs).toLp _
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp (f + g)) hbound hsupport hs),
          Lp.coeFn_add f g,
          Lp.coeFn_add ((memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs).toLp _)
            ((memLp_cutoff hp hχ (Lp.memLp g) hbound hsupport hs).toLp _),
          MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs),
          MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp g) hbound hsupport hs)] with x h₁ h₂ h₃ h₄ h₅
        simp_all only [Pi.add_apply, smul_add]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp (c • f)) hbound hsupport hs),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs).toLp _),
          MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs)] with x h₁ h₂ h₃ h₄
        simp_all only [Pi.smul_apply, RingHom.id_apply, smul_comm (χ x) c] }
  refine T.mkContinuous ((μ s).toReal ^ (1 / 2 - 1 / (p : ℝ))) fun f ↦ ?_
  change ‖(memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (supportExponent_nonneg hp) hs)
      (Lp.memLp f).eLpNorm_ne_top)
    (eLpNorm_cutoff_le hp hχ (Lp.aestronglyMeasurable f) hbound hsupport)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow] using h

/-- The constructed cutoff agrees almost everywhere with pointwise multiplication
(`app:ch_regular:thm:exact-correction`). -/
theorem cutoffL2_coeFn (hp : 2 ≤ p) {χ : α → ℝ} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hsupport : Function.support χ ⊆ s) (hs : μ s ≠ ∞) (f : Lp F p μ) :
    cutoffL2 hp hχ hbound hsupport hs f =ᵐ[μ] fun x ↦ χ x • f x :=
  MemLp.coeFn_toLp (memLp_cutoff hp hχ (Lp.memLp f) hbound hsupport hs)

/-- The operator-norm form of the Hölder support estimate
(`app:ch_regular:thm:exact-correction`). -/
theorem norm_cutoffL2_le (hp : 2 ≤ p) {χ : α → ℝ} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hsupport : Function.support χ ⊆ s) (hs : μ s ≠ ∞) :
    ‖cutoffL2 (F := F) hp hχ hbound hsupport hs‖ ≤
      (μ s).toReal ^ (1 / 2 - 1 / (p : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [Lp.norm_def, eLpNorm_congr_ae (cutoffL2_coeFn hp hχ hbound hsupport hs f),
    Lp.norm_def]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (supportExponent_nonneg hp) hs)
      (Lp.memLp f).eLpNorm_ne_top)
    (eLpNorm_cutoff_le hp hχ (Lp.aestronglyMeasurable f) hbound hsupport)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow] using h

/-- Localizing an L²-to-Lᵖ operator gives the small-support bound of
`app:ch_regular:thm:exact-correction`. An input cutoff can be included as any
L² contraction `B`. The constant is uniform for a family with `‖R‖ ≤ C`. -/
theorem norm_localized_le (hp : 2 ≤ p) {χ : α → ℝ} {s : Set α}
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ x, ‖χ x‖ ≤ 1)
    (hsupport : Function.support χ ⊆ s) (hs : μ s ≠ ∞)
    (R : Lp F 2 μ →L[ℝ] Lp F p μ) (B : Lp F 2 μ →L[ℝ] Lp F 2 μ)
    {C : ℝ} (hR : ‖R‖ ≤ C) (hB : ‖B‖ ≤ 1) :
    ‖(cutoffL2 hp hχ hbound hsupport hs).comp (R.comp B)‖ ≤
      (μ s).toReal ^ (1 / 2 - 1 / (p : ℝ)) * C := by
  have hC : 0 ≤ C := (norm_nonneg R).trans hR
  calc
    _ ≤ ‖cutoffL2 (F := F) hp hχ hbound hsupport hs‖ * (‖R‖ * ‖B‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (R.opNorm_comp_le B) (norm_nonneg _))
    _ ≤ (μ s).toReal ^ (1 / 2 - 1 / (p : ℝ)) * (C * 1) := by
      gcongr
      exact norm_cutoffL2_le hp hχ hbound hsupport hs
    _ = _ := by rw [mul_one]

end SmallSupport
end JanetCartan
