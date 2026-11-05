module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.CoordinateFourier.Parameter

/-!
# Coordinate Fourier symbols and the full initial weight

Each of the three coordinate directions is a unit Hilbert vector. The exact
`2π` parameter multiplier is consequently bounded by the full initial
Bessel weight, as needed by `norm_rawTestSobolev_inputCoordinateTest_le` for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n k : ℕ}

/-- Measurability of the concrete parameter Fourier monomial, used to pass
from nested a.e. identities to the literal product measure in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem measurable_inputCoordinateSymbol (a : Fin k → (Unit ⊕ Fin 2)) :
    Measurable (inputCoordinateSymbol a) := by
  have hc : Continuous (fun z : CarrierParameter => WithLp.toLp 2 z) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)).symm.continuous
  apply Continuous.measurable
  unfold inputCoordinateSymbol
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_finsetProd _ fun _ _ => (hc.inner continuous_const).neg))

/-- The coordinate multiplier is bounded by the full initial weight, with
constant one and including zero transverse dimension. This supplies the
pointwise bound for `norm_rawTestSobolev_inputCoordinateTest_le` in
`app:ch_background:prop:bg-adjoint`. -/
theorem norm_inputCoordinateSymbol_le_initialWeight (a : Fin k → (Unit ⊕ Fin 2))
    (ξ : CarrierVariable n) :
    ‖inputCoordinateSymbol a ξ.1‖ ≤ initialWeight k ξ := by
  have hp : (∏ j, |inner ℝ (WithLp.toLp 2 ξ.1)
      (WithLp.toLp 2 (inputCarrierBasis (a j)))|) ≤ ‖WithLp.toLp 2 ξ.1‖ ^ k := by
    calc
      _ ≤ ∏ _ : Fin k, ‖WithLp.toLp 2 ξ.1‖ := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro j _
        simpa only [norm_toLp_inputCarrierBasis, mul_one] using
          abs_real_inner_le_norm (WithLp.toLp 2 ξ.1)
            (WithLp.toLp 2 (inputCarrierBasis (a j)))
      _ = _ := by simp
  have hbase : 2 * Real.pi * ‖WithLp.toLp 2 ξ.1‖ ≤
      Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖initialCoordinates n ξ‖ ^ 2) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [mul_pow, initialCoordinates_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.fst, WithLp.snd, Real.norm_eq_abs]
    nlinarith [sq_nonneg ‖ξ.2‖, sq_nonneg (2 * Real.pi)]
  calc
    ‖inputCoordinateSymbol a ξ.1‖ = (2 * Real.pi) ^ k *
        ∏ j, |inner ℝ (WithLp.toLp 2 ξ.1)
          (WithLp.toLp 2 (inputCarrierBasis (a j)))| := by
      simp only [inputCoordinateSymbol, norm_mul, norm_pow, norm_neg,
        Complex.norm_ofNat, Complex.norm_real, norm_prod, Real.norm_eq_abs,
        abs_of_nonneg Real.pi_nonneg, Complex.norm_I, mul_one]
    _ ≤ (2 * Real.pi) ^ k * ‖WithLp.toLp 2 ξ.1‖ ^ k :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 * Real.pi * ‖WithLp.toLp 2 ξ.1‖) ^ k := (mul_pow ..).symm
    _ ≤ (Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖initialCoordinates n ξ‖ ^ 2)) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ = initialWeight k ξ := by
      rw [initialWeight, Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]

/-- Multiplying the order-`t` weight by a coordinate derivative symbol costs
exactly `k` Sobolev orders. This is the pointwise integrand estimate consumed
by `norm_rawTestSobolev_inputCoordinateTest_le` for
`app:ch_background:eq:bg-density-adjoint`. -/
theorem initialWeight_mul_norm_inputCoordinateSymbol_le (t : ℕ)
    (a : Fin k → (Unit ⊕ Fin 2)) (ξ : CarrierVariable n) :
    initialWeight t ξ * ‖inputCoordinateSymbol a ξ.1‖ ≤ initialWeight (k + t) ξ := by
  calc
    _ ≤ initialWeight t ξ * initialWeight k ξ :=
      mul_le_mul_of_nonneg_left (norm_inputCoordinateSymbol_le_initialWeight a ξ)
        (initialWeight_pos t ξ).le
    _ = initialWeight (k + t) ξ := by
      simp only [initialWeight, Nat.cast_add, add_div]
      rw [Real.rpow_add (by positivity)]
      exact mul_comm _ _

end JanetCartan.ContinuumAdjoint.DensityMultiplier
