module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.LiteralAdjoint.Membership
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong convergence of the finite carrier adjoints

Dominated convergence on the original carrier measure removes the radial
mask in `app:ch_background:eq:bg-full-complex-amplitude`. Outside the compact
parameter set the literal adjoint is zero; no claim that the parameter-truncated
mask tends globally to one is made. Consumer: identification of the adjoint of
the extension constructed in `Construction`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
variable {n N : ℕ} {d : CarrierData n N}
    {Z : Set CarrierParameter} (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    {κ : ℝ → ℝ} (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1)
    {R : ℕ → ℝ} {M Cmask : ℝ}
    (hmask : ∀ k : ℕ, CarrierRegularization.MaskHypotheses d
      (parameterTruncatedMask Z (radialCarrierMask κ (k + 1))) Z (R k) M Cmask)
include hZ hκone

/-- Strong L² convergence to the literal uncut adjoint, given its membership.
`carrierAdjointIntegral_memLp_bound_of_uniformNormals` supplies that membership
from the actual finite normal bounds. The majorant uses the finite-mask bound
on the angular support and literal vanishing outside it
(`app:ch_background:eq:bg-T` and `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem parameterRegularizedOperator_adjoint_tendsto_literal
    (w : ComplexOutputL2 n)
    (hw : MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n)) :
    Tendsto (fun k ↦ (hmask k).operator.adjoint w) atTop
      (𝓝 (hw.toLp (carrierAdjointIntegral d w))) := by
  let a := hw.toLp (carrierAdjointIntegral d w)
  let m (k : ℕ) := radialCarrierMask κ (k + 1) (n := n)
  have he (k) :
      (fun u ↦ ((hmask k).operator.adjoint w - a) u) =ᵐ[carrierMeasure n]
        fun u ↦ ((m k u : ℂ) - 1) * carrierAdjointIntegral d w u := by
    filter_upwards [Lp.coeFn_sub ((hmask k).operator.adjoint w) a,
      parameterRegularizedOperator_adjoint_ae hZ (hmask k) w, hw.coeFn_toLp]
      with u hs ht ha
    dsimp [a, m] at hs ⊢
    rw [hs, ht, ha]
    ring
  have hsq (k) : ‖(hmask k).operator.adjoint w - a‖ ^ 2 =
      ∫ u, ‖((m k u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2
        ∂carrierMeasure n := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [he k] with u hu
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hu]
  have hlim : Tendsto (fun k ↦ ∫ u,
      ‖((m k u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2 ∂carrierMeasure n)
      atTop (𝓝 0) := by
    have hi := (hw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul
      ((M + 1) ^ 2)
    have ht := tendsto_integral_of_dominated_convergence
      (μ := carrierMeasure n) (f := fun _ ↦ (0 : ℝ))
      (F := fun k u ↦ ‖((m k u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2)
      (fun u ↦ (M + 1) ^ 2 * ‖carrierAdjointIntegral d w u‖ ^ 2)
      (fun k ↦ (((Lp.aestronglyMeasurable ((hmask k).operator.adjoint w - a)).congr
        (he k)).norm.fun_pow 2)) hi ?_ ?_
    · simpa only [integral_zero] using ht
    · intro k
      apply Eventually.of_forall
      intro u
      by_cases hu : u.1 ∈ Z
      · have hb : ‖(m k u : ℂ) - 1‖ ≤ M + 1 := by
          calc
            ‖(m k u : ℂ) - 1‖ ≤ ‖(m k u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ M + 1 := by
              simpa [m, parameterTruncatedMask, hu, Complex.norm_real, Real.norm_eq_abs]
                using add_le_add_right ((hmask k).mask_bound u) 1
        simp only [Real.norm_eq_abs, abs_sq, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
      · simp [carrierAdjointIntegral_eq_zero_outside_parameters d hZ w u hu]
    · apply Eventually.of_forall
      intro u
      apply tendsto_const_nhds.congr'
      filter_upwards [radialCarrierMask_eventually_eq_one κ hκone {u} isCompact_singleton]
        with k hk
      simp [m, hk u (mem_singleton u)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  change Tendsto (fun k ↦ Real.sqrt (∫ u,
    ‖((m k u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2 ∂carrierMeasure n))
    atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [← hsq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end JanetCartan.ContinuumRow.CarrierNormalRealization
