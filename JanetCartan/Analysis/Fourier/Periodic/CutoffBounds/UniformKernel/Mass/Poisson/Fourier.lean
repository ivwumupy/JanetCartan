module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Fourier.Coefficients

/-!
# Poisson identity for the fixed cutoff

For `main:lem:smoothing` and `main:eq:smoothing-low`, the exact fixed periodic
cutoff kernel is the lattice periodization of its Euclidean inverse Fourier
transform. The Schwartz estimates supply convergence and continuity; unfolding
computes the coefficients, and finite Fourier reconstruction identifies the sum.
-/

@[expose] public noncomputable section

open scoped SchwartzMap FourierTransform

namespace JanetCartan

/-- `main:lem:smoothing`: the coefficients of the periodized fixed Euclidean
kernel are exactly the prescribed cutoff symbol, with no change of scale. -/
theorem mFourierCoeff_schwartzTorusPeriodization_cutoffEuclideanKernel
    (n : ℕ) {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff
      (schwartzTorusPeriodization (cutoffEuclideanKernelSchwartz n R hR.ne')) k =
      (periodicCutoffSymbol R k : ℂ) := by
  rw [mFourierCoeff_schwartzTorusPeriodization]
  exact fourier_cutoffEuclideanKernel_integer n hR k

/-- `main:lem:smoothing`: complex Poisson reconstruction for the exact fixed
cutoff on the normalized unit lattice, including dimension zero. -/
theorem sum_periodicCutoffSymbol_mFourier_eq_tsum_cutoffEuclideanKernel
    (n : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ k ∈ periodicCutoffBox n R,
      (periodicCutoffSymbol R k : ℂ) * UnitAddTorus.mFourier k (torusQuotient x)) =
      ∑' k : Fin n → ℤ,
        cutoffEuclideanKernel n R (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  let g := schwartzTorusPeriodization (cutoffEuclideanKernelSchwartz n R hR.ne')
  have hc (k : Fin n → ℤ) : UnitAddTorus.mFourierCoeff g k =
      (periodicCutoffSymbol R k : ℂ) :=
    mFourierCoeff_schwartzTorusPeriodization_cutoffEuclideanKernel n hR k
  have hz : ∀ k ∉ periodicCutoffBox n R, UnitAddTorus.mFourierCoeff g k = 0 := by
    intro k hk
    rw [hc, periodicCutoffSymbol_eq_zero_of_notMem hR hk, Complex.ofReal_zero]
  have hs : Summable (UnitAddTorus.mFourierCoeff g) := summable_of_ne_finset_zero hz
  have he := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusQuotient x)).tsum_eq
  rw [tsum_eq_sum (s := periodicCutoffBox n R) (fun k hk ↦ by rw [hz k hk]; simp)] at he
  simpa only [hc, smul_eq_mul, g, schwartzTorusPeriodization_torusQuotient,
    schwartzLatticePeriodization, cutoffEuclideanKernelSchwartz_apply] using he

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: the fixed real periodic
cutoff kernel equals the absolutely convergent sum of real parts of its
Euclidean kernel over the unit integer lattice. -/
theorem periodicCutoffKernel_eq_tsum_re_cutoffEuclideanKernel
    (n : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    periodicCutoffKernel R (torusQuotient x) =
      ∑' k : Fin n → ℤ,
        (cutoffEuclideanKernel n R (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))).re := by
  have hs : Summable (fun k : Fin n → ℤ ↦
      cutoffEuclideanKernel n R (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) :=
    (summable_norm_schwartz_lattice (cutoffEuclideanKernelSchwartz n R hR.ne') x).of_norm
  have he := congrArg Complex.re
    (sum_periodicCutoffSymbol_mFourier_eq_tsum_cutoffEuclideanKernel n hR x)
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_tsum hs, periodicCutoffKernel] using he

end JanetCartan
