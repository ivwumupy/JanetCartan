module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Literal oscillatory kernel variation at fixed frequency

The original phase, normal field, reduced covector and common masks are kept.
Finite-jet continuity of the actual retained charts is supplied by
`RetainedLeading.exists_originalScalar_immersion_sub_tolerance`. These elementary
bounds turn its zeroth-order field differences into finite-frequency kernel
closeness, for the strong raw-adjoint estimate in
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow

variable {n N : ℕ}

private theorem norm_exp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ ‖a - b‖ := by
  have he : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The real normal-square/reduced-covector amplitude has an explicit local
Lipschitz bound from the actual field differences. No density or source is
replaced (`app:ch_background:eq:bg-T`). -/
theorem norm_squaredField_sub_le (ν ν₀ : Euclidean N) (q q₀ : Euclidean n)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hν : ‖ν‖ ≤ M) (hν₀ : ‖ν₀‖ ≤ M) (hq : ‖q‖ ≤ M)
    (hdν : ‖ν - ν₀‖ ≤ δ) (hdq : ‖q - q₀‖ ≤ δ) :
    ‖‖ν‖ ^ 2 • q - ‖ν₀‖ ^ 2 • q₀‖ ≤ 3 * M ^ 2 * δ := by
  have hsq : |‖ν‖ ^ 2 - ‖ν₀‖ ^ 2| ≤ 2 * M * δ := by
    calc
      |‖ν‖ ^ 2 - ‖ν₀‖ ^ 2| = |‖ν‖ - ‖ν₀‖| * (‖ν‖ + ‖ν₀‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        ring
      _ ≤ δ * (2 * M) :=
        mul_le_mul ((abs_norm_sub_norm_le ν ν₀).trans hdν)
          (by linarith only [hν, hν₀])
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) hδ
      _ = _ := by ring
  have he : ‖ν‖ ^ 2 • q - ‖ν₀‖ ^ 2 • q₀ =
      (‖ν‖ ^ 2 - ‖ν₀‖ ^ 2) • q + ‖ν₀‖ ^ 2 • (q - q₀) := by
    rw [sub_smul, smul_sub]
    abel
  rw [he]
  calc
    ‖(‖ν‖ ^ 2 - ‖ν₀‖ ^ 2) • q + ‖ν₀‖ ^ 2 • (q - q₀)‖ ≤
        ‖(‖ν‖ ^ 2 - ‖ν₀‖ ^ 2) • q‖ + ‖‖ν₀‖ ^ 2 • (q - q₀)‖ := norm_add_le _ _
    _ = |‖ν‖ ^ 2 - ‖ν₀‖ ^ 2| * ‖q‖ + ‖ν₀‖ ^ 2 * ‖q - q₀‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ν₀‖)]
    _ ≤ (2 * M * δ) * M + M ^ 2 * δ :=
      add_le_add
        (mul_le_mul hsq hq (norm_nonneg _) (by positivity))
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hν₀ 2) hdq
          (norm_nonneg _) (sq_nonneg _))
    _ = _ := by ring

/-- Zeroth-order amplitude size on the same original normal/reduced fields. -/
theorem norm_squaredField_le (ν : Euclidean N) (q : Euclidean n) {M : ℝ}
    (hν : ‖ν‖ ≤ M) (hq : ‖q‖ ≤ M) : ‖‖ν‖ ^ 2 • q‖ ≤ M ^ 3 := by
  calc
    ‖‖ν‖ ^ 2 • q‖ = ‖ν‖ ^ 2 * ‖q‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ν‖)]
    _ ≤ M ^ 2 * M := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hν 2) hq
      (norm_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- Only phase difference times the current amplitude and the literal amplitude
difference occur. This is a fixed-frequency estimate; it does not assert full
uncut Fourier integral operator-norm continuity. -/
theorem norm_oscillatory_amplitude_sub_le (a b : ℝ) (v v₀ : Euclidean n) :
    ‖Complex.exp (Complex.I * (a : ℂ)) • euclideanComplexInclusion v -
        Complex.exp (Complex.I * (b : ℂ)) • euclideanComplexInclusion v₀‖ ≤
      ‖a - b‖ * ‖v‖ + ‖v - v₀‖ := by
  have he : Complex.exp (Complex.I * (a : ℂ)) • euclideanComplexInclusion v -
        Complex.exp (Complex.I * (b : ℂ)) • euclideanComplexInclusion v₀ =
      (Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))) •
        euclideanComplexInclusion v +
        Complex.exp (Complex.I * (b : ℂ)) • euclideanComplexInclusion (v - v₀) := by
    rw [map_sub, sub_smul, smul_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Complex.norm_exp_I_mul_ofReal, euclideanComplexInclusion_norm, one_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right (norm_exp_I_sub_le a b) (norm_nonneg _)) le_rfl

/-- The same output chart reduces raw-kernel variation to its actual phase and
amplitude differences. The external, angular and high-pass masks remain inside
the original carrier amplitude (`app:ch_background:eq:bg-T`). -/
theorem norm_carrierKernel_sub_le (d d₀ : CarrierData n N)
    (hchart : d.outputChart = d₀.outputChart) (x : Torus n) (u : CarrierVariable n) :
    ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤
      ‖carrierPhase d x u - carrierPhase d₀ x u‖ * ‖carrierAmplitude d x u‖ +
        ‖carrierAmplitude d x u - carrierAmplitude d₀ x u‖ := by
  classical
  by_cases hx : x ∈ d.outputChart
  · have hx₀ : x ∈ d₀.outputChart := hchart ▸ hx
    simp only [carrierKernel, Set.indicator_of_mem hx, Set.indicator_of_mem hx₀]
    exact norm_oscillatory_amplitude_sub_le _ _ _ _
  · rw [carrierKernel_eq_zero_outside d hx,
      carrierKernel_eq_zero_outside d₀ (hchart ▸ hx)]
    simp only [sub_self, norm_zero]
    positivity

end JanetCartan.PhysicalInverseContinuity
