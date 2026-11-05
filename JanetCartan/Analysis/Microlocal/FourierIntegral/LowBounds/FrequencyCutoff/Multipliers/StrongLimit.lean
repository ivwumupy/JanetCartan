module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers.L2

/-! # Strong convergence of the actual frequency cutoffs

Dominated convergence supplies the strong limit used to remove the
regularization in `app:ch_regular_base:thm:actual-calculus`, Step 1.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform Filter
open scoped Topology ComplexInnerProductSpace
namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "ℰ" => Euclidean n
local notation "𝒱" => EuclideanSpace ℂ (Fin r)
local notation "ℋ" => Lp 𝒱 2 (volume : Measure ℰ)

/-- Dominated convergence for the actual bounded frequency multiplication,
consumed by `multiplier_tendsto` (same Step 1). -/
theorem frequencyMultiplication_tendsto (f : ℋ) :
    Tendsto (fun j ↦ frequencyMultiplication j f) atTop (𝓝 f) := by
  let d : ℕ → ℰ → 𝒱 := fun j ξ ↦ cycleCutoff j ξ • f ξ - f ξ
  have hd (j : ℕ) : AEStronglyMeasurable (d j) volume :=
    ((cycleCutoff_contDiff j).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f)).sub (Lp.aestronglyMeasurable f)
  have hbound (j : ℕ) (ξ : ℰ) : ‖d j ξ‖ ≤ 2 * ‖f ξ‖ := by
    calc
      _ ≤ ‖cycleCutoff j ξ • f ξ‖ + ‖f ξ‖ := norm_sub_le _ _
      _ ≤ ‖f ξ‖ + ‖f ξ‖ := by
        gcongr
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) (cycleCutoff_norm_le j ξ)
      _ = _ := by ring
  have hi : Tendsto (fun j ↦ ∫ ξ, ⟪d j ξ, d j ξ⟫) atTop (𝓝 (0 : ℂ)) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℰ)) (F := fun j ξ ↦ ⟪d j ξ, d j ξ⟫)
      (f := fun _ ↦ (0 : ℂ)) (fun ξ ↦ 4 * ‖f ξ‖ ^ 2)
    simp only [integral_zero] at h
    apply h
    · intro j
      exact (hd j).inner (hd j)
    · exact ((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul 4
    · intro j
      filter_upwards [] with ξ
      calc
        ‖⟪d j ξ, d j ξ⟫‖ ≤ ‖d j ξ‖ * ‖d j ξ‖ := norm_inner_le_norm _ _
        _ ≤ (2 * ‖f ξ‖) * (2 * ‖f ξ‖) :=
          mul_le_mul (hbound j ξ) (hbound j ξ) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · filter_upwards [] with ξ
      have hlim : Tendsto (fun j ↦ d j ξ) atTop (𝓝 (0 : 𝒱)) := by
        simpa [d] using ((cycleCutoff_tendsto ξ).smul (tendsto_const_nhds (x := f ξ))).sub
          (tendsto_const_nhds (x := f ξ))
      simpa only [inner_zero_left] using hlim.inner (𝕜 := ℂ) hlim
  have he (j : ℕ) : ‖frequencyMultiplication j f - f‖ =
      Real.sqrt (Complex.re (∫ ξ, ⟪d j ξ, d j ξ⟫)) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), L2.inner_def]
    apply congrArg Real.sqrt
    apply congrArg Complex.re
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (frequencyMultiplication j f) f,
      frequencyMultiplication_coeFn j f] with ξ hs hm
    rw [hs, Pi.sub_apply, hm]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [he]
  simpa only [Function.comp_def, Complex.zero_re, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp
    (Complex.continuous_re.tendsto 0 |>.comp hi)

/-- Strong convergence `P_j f → f` on the very same vector L² as the graph,
for `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem multiplier_tendsto (f : ℋ) :
    Tendsto (fun j ↦ multiplier j f) atTop (𝓝 f) := by
  simpa only [Function.comp_def, fourierInvCLM_apply, multiplier_apply, fourierInv_fourier_eq] using
    (fourierInvCLM ℂ ℋ).continuous.tendsto (𝓕 f) |>.comp
      (frequencyMultiplication_tendsto (𝓕 f))

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
