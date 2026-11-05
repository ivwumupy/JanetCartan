module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise.CubeEstimate.Coordinates
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise.CubeEstimate.Marginal

/-!
# Unit-cube averaging estimates

Iterating the averaged fundamental theorem of calculus over all coordinates
bounds a smooth function by the local L¹ norms of its derivatives through the
dimension. This is the pointwise estimate used in
`app:ch_regular:thm:exact-correction`, with derivative norms as in
`app:not:fourier`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

/-- The iterated averaged FTC bound on a unit cube for the Sobolev norms of
`app:not:fourier`, used in `app:ch_regular:thm:exact-correction`. This holds for
arbitrary normed real targets in every dimension, including zero, without
support or integrability assumptions. -/
theorem enorm_le_sum_lintegral_iteratedFDeriv_pointwiseUnitCube
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : EuclideanSpace ℝ (Fin n) → F} (hu : ContDiff ℝ ∞ u)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖u x‖ₑ ≤ (2 : ℝ≥0∞) ^ n * ∑ l ∈ Finset.range (n + 1),
      ∫⁻ y in pointwiseUnitCube x, ‖iteratedFDeriv ℝ l u y‖ₑ := by
  have hmeas (l : ℕ) : Measurable (fun y ↦ ‖iteratedFDeriv ℝ l u y‖ₑ) :=
    (hu.continuous_iteratedFDeriv (by simp)).enorm.measurable
  have h := le_two_pow_mul_sum_lintegral_Icc_of_coordinate_bounds n (WithLp.ofLp x)
    (fun l z ↦ ‖iteratedFDeriv ℝ l u (WithLp.toLp 2 z)‖ₑ)
    (fun l ↦ (hmeas l).comp (PiLp.volume_preserving_toLp (Fin n)).measurable)
    (by
      intro l i z hz
      simpa only [← hz] using enorm_iteratedFDeriv_le_coordinate_integrals hu l z i)
  simp_rw [← lintegral_pointwiseUnitCube_eq_pi (hmeas _) x] at h
  simpa only [WithLp.toLp_ofLp, ← ofReal_norm, norm_iteratedFDeriv_zero] using h

end JanetCartan.LocalSobolev.FiniteOrder
