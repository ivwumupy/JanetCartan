module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Realization.Character
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Integral
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff
public import JanetCartan.Analysis.Fourier.Periodic.Deriv
public import JanetCartan.Analysis.Fourier.Periodic.Lattice
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scalar realization of the periodic cutoff

For `main:eq:smoothing-high`, absolute convergence and dominated convergence identify
the Euclidean integral with the fixed finite Fourier multiplier.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ}

/-- `main:lem:smoothing`: smooth real fields have absolutely summable complex
Fourier coefficients. This uses the published polynomial decay estimate. -/
theorem IsSmoothPeriodic.summable_norm_mFourierCoeff_ofReal {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) :
    Summable (fun k ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖) := by
  obtain ⟨C, _hC, hdecay⟩ := hf.exists_mFourierCoeff_decay (n + 1)
  have hsum := (summable_frequencyNorm_rpow (n := n)
    (p := (n + 1 : ℕ)) (by push_cast; linarith)).mul_left C
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
  rw [norm_norm]
  calc
    _ ≤ C / frequencyNorm k ^ (n + 1) := hdecay k hk
    _ = C * frequencyNorm k ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (frequencyNorm_nonneg k), Real.rpow_natCast, div_eq_mul_inv]

/-- `main:eq:smoothing-high`: smooth scalar fields admit termwise integration
against the fixed Euclidean cutoff kernel. -/
theorem hasSum_integral_cutoffSchwartzKernel_fourier {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun k ↦
      (periodicCutoffSymbol R k : ℂ) *
        UnitAddTorus.mFourierCoeff (fun z ↦ (f z : ℂ)) k *
          periodicLift (UnitAddTorus.mFourier k) x)
      ((cutoffEuclideanConvolution R f x : ℝ) : ℂ) := by
  let c := UnitAddTorus.mFourierCoeff (fun z ↦ (f z : ℂ))
  let g : C(Torus n, ℂ) := ⟨fun z ↦ (f z : ℂ), Complex.continuous_ofReal.comp hf.1⟩
  have hs : Summable (fun k ↦ ‖c k‖) := hf.summable_norm_mFourierCoeff_ofReal
  have hchar (k : Fin n → ℤ) (z : EuclideanSpace ℝ (Fin n)) :
      ‖periodicLift (UnitAddTorus.mFourier k) z‖ = 1 := by
    simp [periodicLift, UnitAddTorus.mFourier, fourier_apply, norm_prod]
  let term := fun (k : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)) ↦
    (cutoffSchwartzKernel n y : ℂ) *
      (c k * periodicLift (UnitAddTorus.mFourier k) (x - (2 * Real.pi / R) • y))
  have hm (k : Fin n → ℤ) : AEStronglyMeasurable (term k) := by
    apply Continuous.aestronglyMeasurable
    exact ((Complex.continuous_ofReal.comp (cutoffSchwartzKernel n).continuous).mul
      (continuous_const.mul ((contDiff_periodicLift_mFourier k).continuous.comp
        (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin n) ↦
          x - (2 * Real.pi / R) • y)))))
  have hbound (k : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)) :
      ‖term k y‖ ≤ ‖cutoffSchwartzKernel n y‖ * ‖c k‖ := by
    simp [term, hchar]
  have hi := hasSum_integral_of_dominated_convergence
    (fun k y ↦ ‖cutoffSchwartzKernel n y‖ * ‖c k‖) hm
    (fun k ↦ Filter.Eventually.of_forall (hbound k))
    (Filter.Eventually.of_forall (fun y ↦ hs.mul_left ‖cutoffSchwartzKernel n y‖))
    (show Integrable (fun y ↦ ∑' k, ‖cutoffSchwartzKernel n y‖ * ‖c k‖) from by
      simp_rw [tsum_mul_left]
      exact (cutoffSchwartzKernel n).integrable.norm.mul_const _)
    (f := fun y ↦ (cutoffSchwartzKernel n y : ℂ) *
      ((periodicLift f (x - (2 * Real.pi / R) • y) : ℝ) : ℂ))
    (Filter.Eventually.of_forall (fun y ↦ by
      exact (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := g) hs.of_norm (torusQuotient (x - (2 * Real.pi / R) • y))).mul_left
          (cutoffSchwartzKernel n y : ℂ)))
  have hterm (k : Fin n → ℤ) : (∫ y, term k y) =
      (periodicCutoffSymbol R k : ℂ) * c k *
        periodicLift (UnitAddTorus.mFourier k) x := by
    simp only [term, mul_left_comm _ (c k)]
    rw [integral_const_mul, integral_cutoffSchwartzKernel_mFourier]
    ring
  simp_rw [hterm] at hi
  convert hi using 1
  · simp only [cutoffEuclideanConvolution, smul_eq_mul, ← integral_complex_ofReal,
      Complex.ofReal_mul]

/-- `main:eq:smoothing-high`: the Euclidean Schwartz-kernel convolution equals
the actual periodic cutoff for smooth real scalar fields. -/
theorem cutoffEuclideanConvolution_eq_periodicCutoff_scalar {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin n)) :
    cutoffEuclideanConvolution R f x = periodicLift (periodicCutoff R f) x := by
  apply Complex.ofReal_injective
  rw [periodicLift, Function.comp_apply, ofReal_periodicCutoff hf.1]
  apply (hasSum_integral_cutoffSchwartzKernel_fourier hf R x).unique
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  simp [periodicCutoffSymbol_eq_zero_of_notMem hR hk]

end JanetCartan
