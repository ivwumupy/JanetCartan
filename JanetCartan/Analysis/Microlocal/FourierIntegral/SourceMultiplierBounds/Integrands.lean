module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplierBounds.Moments
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact local expressions for the source remainder

These are the endpoint difference and the FTC integrand printed after
`app:ch_regular_base:eq:fixed-source-multiplication`, at a fixed output point.
The target can be the full complex matrix space with its Frobenius norm.
Only scalar multiplication occurs, so matrix factors are never commuted.
Identification with the graph source multiplier belongs to `SourceMultiplier`;
the bounds accept the exact FTC equality as an explicit input.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace JanetCartan.FourierIntegral.SourceBounds

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The exact two endpoint terms of the source remainder, in physical covectors
(`app:ch_regular_base:eq:fixed-source-multiplication`). -/
def endpointDifference (S : Euclidean n → ℝ) (A : Euclidean n → F)
    (η v : Euclidean n) : F :=
  Complex.exp (Complex.I * ((S (η + v) - S η : ℝ) : ℂ)) • A (η + v) -
    Complex.exp (Complex.I * ((fderiv ℝ S η v : ℝ) : ℂ)) • A η

/-- The actual interpolating-phase derivative in the source FTC formula.
The two terms are `v · A_η` and `i (S_η(η+tv)-S_η(η))·v A`.
Source: proof after `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def ftcIntegrand (S : Euclidean n → ℝ) (A : Euclidean n → F)
    (η v : Euclidean n) (t : ℝ) : F :=
  Complex.exp (Complex.I *
    ((S (η + t • v) - S η + (1 - t) * fderiv ℝ S η v : ℝ) : ℂ)) •
    (fderiv ℝ A (η + t • v) v +
      (Complex.I * (((fderiv ℝ S (η + t • v) - fderiv ℝ S η) v : ℝ) : ℂ)) •
        A (η + t • v))

/-- The exact remainder integral against the fixed physical Fourier density.
The graph-operator identity is a separate obligation of `SourceMultiplier`.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceRemainder (m : 𝓢(Euclidean n, ℂ)) (S : Euclidean n → ℝ)
    (A : Euclidean n → F) (η : Euclidean n) : F :=
  ∫ v, physicalSourceDensity m v • endpointDifference S A η v

/-- The physical exponential is unit modulus; in particular no exponential
phase bound is needed for the far tail of the source formula. -/
theorem norm_physical_exp (a : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

/-- A global bound on the actual extended amplitude bounds the two far-region
endpoints, including low-frequency and angular shoulders. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem norm_endpointDifference_le (S : Euclidean n → ℝ) (A : Euclidean n → F)
    {C : ℝ} (hA : ∀ ξ, ‖A ξ‖ ≤ C) (η v : Euclidean n) :
    ‖endpointDifference S A η v‖ ≤ 2 * C := by
  unfold endpointDifference
  calc
    _ ≤ ‖Complex.exp (Complex.I * ((S (η + v) - S η : ℝ) : ℂ)) • A (η + v)‖ +
        ‖Complex.exp (Complex.I * ((fderiv ℝ S η v : ℝ) : ℂ)) • A η‖ := norm_sub_le _ _
    _ = ‖A (η + v)‖ + ‖A η‖ := by simp only [norm_smul, norm_physical_exp, one_mul]
    _ ≤ 2 * C := by linarith [hA (η + v), hA η]

/-- Continuity of the actual endpoint integrand in the integration covector,
used to establish absolute convergence of the source formula. -/
theorem continuous_endpointDifference (S : Euclidean n → ℝ) (A : Euclidean n → F)
    (hS : Continuous S) (hA : Continuous A) (η : Euclidean n) :
    Continuous (endpointDifference S A η) := by
  unfold endpointDifference
  fun_prop

/-- Absolute convergence against the same fixed cutoff, for order zero and
order minus one amplitudes with bounded smooth extensions. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem integrable_sourceRemainder (m : 𝓢(Euclidean n, ℂ))
    (S : Euclidean n → ℝ) (A : Euclidean n → F)
    (hS : Continuous S) (hA : Continuous A) {C : ℝ}
    (hbound : ∀ ξ, ‖A ξ‖ ≤ C) (η : Euclidean n) :
    Integrable (fun v ↦ physicalSourceDensity m v • endpointDifference S A η v) := by
  apply ((physicalSourceDensity m).integrable.norm.mul_const (2 * C)).mono'
    (((physicalSourceDensity m).continuous.smul
      (continuous_endpointDifference S A hS hA η)).aestronglyMeasurable)
  filter_upwards [] with v
  change ‖physicalSourceDensity m v • endpointDifference S A η v‖ ≤
    ‖physicalSourceDensity m v‖ * (2 * C)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_endpointDifference_le S A hbound η v)
    (norm_nonneg (physicalSourceDensity m v))

end JanetCartan.FourierIntegral.SourceBounds
