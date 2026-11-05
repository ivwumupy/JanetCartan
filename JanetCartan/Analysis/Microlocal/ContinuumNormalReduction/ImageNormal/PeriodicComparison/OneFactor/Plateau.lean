module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# An interior output plateau for the one-factor comparison

The one-inverse comparison in `app:ch_background:prop:bg-frame`, Step 1,
must be differentiated before applying the measurement cutoff. A product of
one-dimensional smooth bumps supplies an output plateau in a strictly larger
interior cube. Local equality, including first derivatives, removes every
plateau defect where the measurement cutoff acts.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A smooth output plateau exists in a strictly larger cube inside the
centered cell. It equals one on a neighborhood of every point of the original
cube, even when that cube is empty. This supplies the localization in the
one-factor comparison of `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_oneFactorPlateau {r : ℝ} (hr : r < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ r < R ∧ R < 1 / 2 ∧ ∃ ρ : E → ℝ,
      ContDiff ℝ ∞ ρ ∧ tsupport ρ ⊆ chartBox R ∧
        ∀ x ∈ chartBox r, ρ =ᶠ[nhds x] (fun _ ↦ 1) := by
  have hm : max r 0 < (1 / 2 : ℝ) := max_lt hr (by norm_num)
  obtain ⟨R, hR₀, hR⟩ := exists_between hm
  obtain ⟨s, hs₀, hs⟩ := exists_between hR₀
  have hspos : 0 < s := (le_max_right r 0).trans_lt hs₀
  have hrs : r < s := (le_max_left r 0).trans_lt hs₀
  let b : ContDiffBump (0 : ℝ) := ⟨s, R, hspos, hs⟩
  let ρ : E → ℝ := fun x ↦ ∏ a, b (x a)
  refine ⟨R, hspos.trans hs, hrs.trans hs, hR, ρ, ?_, ?_, ?_⟩
  · exact contDiff_prod fun a _ ↦ b.contDiff.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) a).contDiff
  · intro x hx
    apply imageBessel_cube_bounds_of_mem_tsupport ρ _ hx
    intro y hy a
    have hb : b (y a) ≠ 0 := by
      intro hb
      exact hy (Finset.prod_eq_zero (Finset.mem_univ a) hb)
    have hball : y a ∈ Metric.ball (0 : ℝ) R := b.support_eq ▸ hb
    exact le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hball)
  · intro x hx
    have hb (a : Fin d) : (fun y : E ↦ b (y a)) =ᶠ[nhds x] (fun _ ↦ 1) :=
      (b.eventuallyEq_one_of_mem_ball (by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
          (show |(EuclideanSpace.proj a) x| < b.rIn from (hx a).trans_lt hrs))).comp_tendsto
            (EuclideanSpace.proj a).continuous.continuousAt
    filter_upwards [Filter.eventually_all.mpr hb] with y hy
    exact Finset.prod_eq_one fun a _ ↦ hy a

/-- The auxiliary plateau and all of its first-order defects disappear
under the original measurement cutoff. The equality is a consequence of
local equality of functions, so no differentiability of the input is assumed
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem maskedCoefficientOperator_plateau (ρ μ : E → ℝ)
    (hρ : ∀ x ∈ tsupport μ, ρ =ᶠ[nhds x] (fun _ ↦ 1))
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (u : E → Fin d → ℂ) (x : E) (i : Fin d) :
    (μ x : ℂ) * coefficientOperator A Z (fun y j ↦ (ρ y : ℂ) * u y j) x i =
      (μ x : ℂ) * coefficientOperator A Z u x i := by
  by_cases hμ : μ x = 0
  · simp [hμ]
  · have he (j : Fin d) : (fun y ↦ (ρ y : ℂ) * u y j) =ᶠ[nhds x] (fun y ↦ u y j) := by
      filter_upwards [hρ x (subset_tsupport μ hμ)] with y hy
      simp [hy]
    simp only [coefficientOperator, partialDeriv, (he _).fderiv_eq, (he _).self_of_nhds]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
