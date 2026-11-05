module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PhysicalSeries

/-!
# Dominated convergence for the coefficient multipliers

The multiplier step of `app:ch_osc:lem:osc-amplitude`, consumed by
`PdoLimit.tendsto_twoPositionL2Operator`. The dominating square is constructed
from the common symbol bound and the actual L² input.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal ComplexInnerProductSpace
open JanetCartan.AmplitudeBound
namespace JanetCartan.FourierIntegral.UncutNormal.PdoLimit
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp ℂ 2 (volume : Measure E)

/-- Uniformly bounded, almost everywhere convergent symbols act strongly
continuously on L². This supplies the multiplier limit for the physical Fourier
series in `app:ch_osc:lem:osc-amplitude`. -/
theorem tendsto_multiplicationOperator_of_ae
    (a : ℕ → Lp ℂ ∞ (volume : Measure E)) (b : Lp ℂ ∞ (volume : Measure E))
    {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ m, ∀ᵐ ξ, ‖a m ξ‖ ≤ C) (hb : ∀ᵐ ξ, ‖b ξ‖ ≤ C)
    (hlim : ∀ᵐ ξ, Tendsto (fun m ↦ a m ξ) atTop (𝓝 (b ξ))) (f : H) :
    Tendsto (fun m ↦ multiplicationOperator (a m) f) atTop
      (𝓝 (multiplicationOperator b f)) := by
  let d : ℕ → E → ℂ := fun m ξ ↦ a m ξ * f ξ - b ξ * f ξ
  have hd (m : ℕ) : AEStronglyMeasurable (d m) volume :=
    ((Lp.aestronglyMeasurable (a m)).mul (Lp.aestronglyMeasurable f)).sub
      ((Lp.aestronglyMeasurable b).mul (Lp.aestronglyMeasurable f))
  have hbound (m : ℕ) : ∀ᵐ ξ, ‖d m ξ‖ ≤ (2 * C) * ‖f ξ‖ := by
    filter_upwards [ha m, hb] with ξ hma hmb
    calc
      _ ≤ ‖a m ξ * f ξ‖ + ‖b ξ * f ξ‖ := norm_sub_le _ _
      _ ≤ C * ‖f ξ‖ + C * ‖f ξ‖ := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hma (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hmb (norm_nonneg _))
      _ = _ := by ring
  have hi : Tendsto (fun m ↦ ∫ ξ, ⟪d m ξ, d m ξ⟫) atTop (𝓝 (0 : ℂ)) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure E)) (F := fun m ξ ↦ ⟪d m ξ, d m ξ⟫)
      (f := fun _ ↦ (0 : ℂ)) (fun ξ ↦ (2 * C)^2 * ‖f ξ‖^2)
    simp only [integral_zero] at h
    apply h
    · intro m
      exact (hd m).inner (hd m)
    · exact ((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul _
    · intro m
      filter_upwards [hbound m] with ξ hξ
      calc
        ‖⟪d m ξ, d m ξ⟫‖ ≤ ‖d m ξ‖ * ‖d m ξ‖ := norm_inner_le_norm _ _
        _ ≤ ((2 * C) * ‖f ξ‖) * ((2 * C) * ‖f ξ‖) :=
          mul_le_mul hξ hξ (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · filter_upwards [hlim] with ξ hξ
      have ht : Tendsto (fun m ↦ d m ξ) atTop (𝓝 (0 : ℂ)) := by
        simpa [d] using (hξ.mul_const (f ξ)).sub (tendsto_const_nhds (x := b ξ * f ξ))
      simpa only [inner_zero_left] using ht.inner (𝕜 := ℂ) ht
  have he (m : ℕ) : ‖multiplicationOperator (a m) f - multiplicationOperator b f‖ =
      Real.sqrt (Complex.re (∫ ξ, ⟪d m ξ, d m ξ⟫)) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), L2.inner_def]
    apply congrArg Real.sqrt
    apply congrArg Complex.re
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (multiplicationOperator (a m) f) (multiplicationOperator b f),
      multiplicationOperator_coeFn (a m) f, multiplicationOperator_coeFn b f] with ξ hs hma hmb
    rw [hs, Pi.sub_apply, hma, hmb]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [he]
  simpa only [Function.comp_def, Complex.zero_re, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp (Complex.continuous_re.tendsto 0 |>.comp hi)

/-- Plancherel transports the proved multiplication limit to the actual Fourier
multipliers in `app:ch_osc:lem:osc-amplitude`. -/
theorem tendsto_fourierMultiplier_of_ae
    (a : ℕ → Lp ℂ ∞ (volume : Measure E)) (b : Lp ℂ ∞ (volume : Measure E))
    {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ m, ∀ᵐ ξ, ‖a m ξ‖ ≤ C) (hb : ∀ᵐ ξ, ‖b ξ‖ ≤ C)
    (hlim : ∀ᵐ ξ, Tendsto (fun m ↦ a m ξ) atTop (𝓝 (b ξ))) (f : H) :
    Tendsto (fun m ↦ fourierMultiplier (a m) f) atTop
      (𝓝 (fourierMultiplier b f)) :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.continuous.continuousAt.tendsto.comp
    (tendsto_multiplicationOperator_of_ae a b hC ha hb hlim
      (Lp.fourierTransformₗᵢ E ℂ f))

end JanetCartan.FourierIntegral.UncutNormal.PdoLimit
