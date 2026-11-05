module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Frequency integration by parts for full kernels

The frequency-regularized calculus in `app:ch_regular_base:eq:actual-pdo-remainder`.
Frequencies here are cycles per unit length, so the phase is `2π (x-y)·ξ` and the
integration-by-parts coefficient is `(2πi)⁻¹`. This agrees with the project's
unit-torus convention. The manuscript's radian frequency is `2πξ`.

The codomain is any complex normed space (including finite matrix spaces with
their chosen norm). All identities concern actual, absolutely integrable kernels.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace JanetCartan.Pseudodifferential

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

-- Supply the canonical operator-norm instance explicitly for the nested space;
-- instance search in the pinned Mathlib version does not find this projection.
local instance : ContinuousENorm (V →L[ℝ] V →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (V →L[ℝ] V →L[ℝ] F) inferInstance).toContinuousENorm

/-- `app:ch_regular_base:thm:actual-calculus`: the Fourier integral of a full
two-position amplitude; physical masks stay inside `c`. -/
def amplitudeKernel (c : V → V → V → F) (x y : V) : F :=
  𝓕 (c x y) (y - x)

/-- `app:ch_regular_base:thm:actual-calculus`: the kernel is the actual integral
with the unit-frequency `2π` phase. -/
theorem amplitudeKernel_eq_integral (c : V → V → V → F) (x y : V) :
    amplitudeKernel c x y =
      ∫ ξ, Complex.exp ((2 * Real.pi * ⟪ξ, x - y⟫ : ℝ) * Complex.I) • c x y ξ := by
  rw [amplitudeKernel, Real.fourier_eq']
  congr 1
  ext ξ
  rw [show y - x = -(x - y) by abel, inner_neg_right]
  congr 2
  push_cast
  ring

/-- `app:ch_regular_base:thm:actual-calculus`: the elementary absolute kernel
bound, before the stronger symbol-to-operator estimates. -/
theorem norm_amplitudeKernel_le (c : V → V → V → F) (x y : V) :
    ‖amplitudeKernel c x y‖ ≤ ∫ ξ, ‖c x y ξ‖ :=
  Real.norm_fourier_le_integral_norm _ _

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: scalar factors commute with
the frequency integral. -/
theorem fourier_const_smul (f : V → F) (z : ℂ) (w : V) :
    𝓕 (fun ξ ↦ z • f ξ) w = z • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ V) f z) w

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: integration by parts in one
frequency direction, for a full matrix-valued amplitude. -/
theorem fourier_directionalDerivative (f : V → F) (v w : V) (hf : Integrable f)
    (hd : Differentiable ℝ f) (hdf : Integrable (fderiv ℝ f)) :
    𝓕 (fun ξ ↦ fderiv ℝ f ξ v) w =
      (2 * Real.pi * Complex.I) • (⟪v, w⟫ • 𝓕 f w) := by
  rw [← Real.fourier_continuousLinearMap_apply hdf, Real.fourier_fderiv hf hd hdf]
  change -(2 * Real.pi * Complex.I) • (-⟪w, v⟫ • 𝓕 f w) = _
  simp only [neg_smul, smul_neg, neg_neg, real_inner_comm]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the finite divergence of the
linear Taylor coefficient in an orthonormal coordinate frame. -/
def frequencyDivergence {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V →L[ℝ] F) (ξ : V) : F :=
  ∑ j, (fderiv ℝ B ξ (b j)) (b j)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the divergence uses exactly
one frequency derivative. The explicit factor is the coordinate dimension. -/
theorem norm_frequencyDivergence_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V → V →L[ℝ] F) (ξ : V) :
    ‖frequencyDivergence b B ξ‖ ≤ Fintype.card ι * ‖fderiv ℝ B ξ‖ := by
  calc
    _ ≤ ∑ j, ‖(fderiv ℝ B ξ (b j)) (b j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, ‖fderiv ℝ B ξ‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖fderiv ℝ B ξ (b j)‖ * ‖b j‖ := (fderiv ℝ B ξ (b j)).le_opNorm _
        _ ≤ (‖fderiv ℝ B ξ‖ * ‖b j‖) * ‖b j‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ B ξ).le_opNorm _) (norm_nonneg _)
        _ = ‖fderiv ℝ B ξ‖ := by simp
    _ = _ := by simp [nsmul_eq_mul]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the Fourier transform of the
finite divergence contracts the full Taylor coefficient with the displacement. -/
theorem fourier_frequencyDivergence {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V → V →L[ℝ] F) (w : V)
    (hB : Integrable B) (hdB : Differentiable ℝ B)
    (hDB : Integrable (fderiv ℝ B)) :
    𝓕 (frequencyDivergence b B) w = (2 * Real.pi * Complex.I) • (𝓕 B w) w := by
  have hpart (j : ι) : Integrable (fun ξ ↦ (fderiv ℝ B ξ (b j)) (b j)) :=
    (hDB.apply_continuousLinearMap (b j)).apply_continuousLinearMap (b j)
  have heq (j : ι) : 𝓕 (fun ξ ↦ (fderiv ℝ B ξ (b j)) (b j)) w =
      (2 * Real.pi * Complex.I) • (⟪b j, w⟫ • (𝓕 B w) (b j)) := by
    rw [← Real.fourier_continuousLinearMap_apply (hDB.apply_continuousLinearMap (b j)),
      fourier_directionalDerivative B (b j) w hB hdB hDB]
    rfl
  calc
    _ = ∑ j, 𝓕 (fun ξ ↦ (fderiv ℝ B ξ (b j)) (b j)) w := by
      simp only [Real.fourier_eq, frequencyDivergence, Finset.smul_sum]
      exact integral_finsetSum _ fun j _ ↦ (Real.fourierIntegral_convergent_iff w).mpr (hpart j)
    _ = (2 * Real.pi * Complex.I) • ∑ j, ⟪b j, w⟫ • (𝓕 B w) (b j) := by
      simp_rw [heq, Finset.smul_sum]
    _ = _ := by simp only [← map_smul, ← map_sum, b.sum_repr']

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the frequency divergence with
the coefficient for the `2π` phase convention. -/
def normalizedFrequencyDivergence {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V →L[ℝ] F) (ξ : V) : F :=
  (2 * Real.pi * Complex.I)⁻¹ • frequencyDivergence b B ξ

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact conversion of a linear
source displacement to a differentiated amplitude, including the phase constant. -/
theorem fourier_normalizedFrequencyDivergence {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V → V →L[ℝ] F) (w : V)
    (hB : Integrable B) (hdB : Differentiable ℝ B)
    (hDB : Integrable (fderiv ℝ B)) :
    𝓕 (normalizedFrequencyDivergence b B) w = (𝓕 B w) w := by
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  change 𝓕 (fun ξ ↦ (2 * Real.pi * Complex.I)⁻¹ • frequencyDivergence b B ξ) w = _
  rw [fourier_const_smul, fourier_frequencyDivergence b B w hB hdB hDB,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

end JanetCartan.Pseudodifferential
