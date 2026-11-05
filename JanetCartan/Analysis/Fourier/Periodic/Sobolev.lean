module

public import JanetCartan.Analysis.Fourier.Periodic.Sobolev.DerivativeEnergy

/-!
# Integer Fourier Sobolev norm comparison

For Appendix A and `app:ch_regular_base:lem:ball-extension`, this file compares
the shared Bessel-potential norm with the L² norm of all Cartesian derivatives
through order `m`. For smooth periodic fields with finite-dimensional real Hilbert
codomain, `periodicSobolevNorm_equiv_derivativeL2Norm` gives the constants `1` and
`sqrt (m!)`. The derivative Fourier identities and Parseval establish convergence
of every series used here, so the final comparison has no summability premise.

The initial spectral inequalities also apply to arbitrary normed real codomains,
with their summability hypothesis explicit.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan

variable {n : ℕ}

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Fourier expression for the sum of squared Cartesian derivative norms through
order `m` (Appendix A; `app:ch_regular_base:lem:ball-extension`). Each multiindex
occurs once. Identification with derivative integrals requires Parseval. -/
def periodicDerivativeFourierEnergy (m : ℕ) (f : Torus n → F) : ℝ :=
  ∑ α ∈ sobolevMultiindices n m, ∑' k : Fin n → ℤ,
    sobolevMonomial α k *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)

/-- Nonnegativity of the derivative Fourier energy (Appendix A). -/
theorem periodicDerivativeFourierEnergy_nonneg (m : ℕ) (f : Torus n → F) :
    0 ≤ periodicDerivativeFourierEnergy m f := by
  apply Finset.sum_nonneg
  intro α _
  apply tsum_nonneg
  intro k
  exact mul_nonneg (sobolevMonomial_nonneg α k) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The derivative Fourier energy is a single weighted series when the shared
Sobolev series is summable (Appendix A). -/
theorem periodicDerivativeFourierEnergy_eq_tsum (m : ℕ) (f : Torus n → F)
    (h : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    periodicDerivativeFourierEnergy m f =
      ∑' k : Fin n → ℤ, sobolevDerivativeWeight m k *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  apply (tsum_sobolevDerivativeWeight m _
    (fun k ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) _).symm
  simpa only [Real.rpow_natCast] using h

/-- The Fourier expression for the derivative norm is bounded by the shared Sobolev
norm with constant `1` (Appendix A; `app:ch_regular_base:lem:ball-extension`).
This is a spectral comparison, before identification with derivative integrals. -/
theorem sqrt_periodicDerivativeFourierEnergy_le (m : ℕ) (f : Torus n → F)
    (h : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    Real.sqrt (periodicDerivativeFourierEnergy m f) ≤ periodicSobolevNorm m f := by
  rw [periodicDerivativeFourierEnergy_eq_tsum m f h, periodicSobolevNorm]
  simp only [Real.rpow_natCast] at h ⊢
  apply Real.sqrt_le_sqrt
  exact (tsum_sobolevWeight_comparison m _
    (fun k ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) h).1

/-- The shared Sobolev norm is bounded by `sqrt (m!)` times the Fourier expression
for the derivative norm (Appendix A; `app:ch_regular_base:lem:ball-extension`).
This is a spectral comparison, before identification with derivative integrals. -/
theorem periodicSobolevNorm_le_sqrt_factorial_mul (m : ℕ) (f : Torus n → F)
    (h : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    periodicSobolevNorm m f ≤
      Real.sqrt (m.factorial : ℝ) * Real.sqrt (periodicDerivativeFourierEnergy m f) := by
  rw [periodicDerivativeFourierEnergy_eq_tsum m f h, periodicSobolevNorm,
    ← Real.sqrt_mul (Nat.cast_nonneg m.factorial)]
  simp only [Real.rpow_natCast] at h ⊢
  apply Real.sqrt_le_sqrt
  exact (tsum_sobolevWeight_comparison m _
    (fun k ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) h).2

end Normed

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Parseval identifies the derivative Fourier energy with the sum of the actual
Cartesian derivative L² energies (Appendix A, `app:not:fourier`;
`app:ch_regular_base:lem:ball-extension`). -/
theorem periodicDerivativeFourierEnergy_eq_sum_l2Norm_sq {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    periodicDerivativeFourierEnergy m f =
      ∑ α ∈ sobolevMultiindices n m,
        periodicL2Norm (periodicMultiindexDeriv (fun i ↦ α (some i)) f) ^ 2 := by
  apply Finset.sum_congr rfl
  intro α _
  exact (hf.hasSum_sobolevMonomial α).tsum_eq

/-- The square root of the Fourier derivative energy is the manuscript's
derivative Sobolev norm (Appendix A, `app:ch_regular_base:lem:ball-extension`). -/
theorem sqrt_periodicDerivativeFourierEnergy_eq {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    Real.sqrt (periodicDerivativeFourierEnergy m f) = periodicDerivativeL2Norm m f := by
  rw [periodicDerivativeFourierEnergy_eq_sum_l2Norm_sq hf]
  rfl

/-- The L² norm of all Cartesian derivatives through order `m` is bounded by the
shared Fourier Sobolev norm with constant `1` (Appendix A,
`app:ch_regular_base:lem:ball-extension`). -/
theorem periodicDerivativeL2Norm_le_periodicSobolevNorm {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    periodicDerivativeL2Norm m f ≤ periodicSobolevNorm m f := by
  rw [← sqrt_periodicDerivativeFourierEnergy_eq hf]
  exact sqrt_periodicDerivativeFourierEnergy_le m f (hf.summable_periodicSobolevNorm m)

/-- The shared Fourier Sobolev norm is bounded by `sqrt (m!)` times the L² norm
of all Cartesian derivatives through order `m` (Appendix A,
`app:ch_regular_base:lem:ball-extension`). -/
theorem periodicSobolevNorm_le_factorial_mul_derivativeL2Norm {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    periodicSobolevNorm m f ≤ Real.sqrt (m.factorial : ℝ) * periodicDerivativeL2Norm m f := by
  rw [← sqrt_periodicDerivativeFourierEnergy_eq hf]
  exact periodicSobolevNorm_le_sqrt_factorial_mul m f (hf.summable_periodicSobolevNorm m)

/-- Equivalence of the Fourier and Cartesian derivative Sobolev norms at every
nonnegative integer order, with constants `1` and `sqrt (m!)` (Appendix A,
`app:not:fourier`; `app:ch_regular_base:lem:ball-extension`). Smoothness supplies
all analytic inputs, including summability of the Fourier Sobolev series. -/
theorem periodicSobolevNorm_equiv_derivativeL2Norm {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (m : ℕ) :
    periodicDerivativeL2Norm m f ≤ periodicSobolevNorm m f ∧
      periodicSobolevNorm m f ≤
        Real.sqrt (m.factorial : ℝ) * periodicDerivativeL2Norm m f :=
  ⟨periodicDerivativeL2Norm_le_periodicSobolevNorm hf m,
    periodicSobolevNorm_le_factorial_mul_derivativeL2Norm hf m⟩

end InnerProduct

end JanetCartan
