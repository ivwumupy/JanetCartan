module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.SchwartzKernel

/-!
# The Euclidean cutoff kernel on torus characters

The normalization bridge for `main:lem:smoothing` and `main:eq:smoothing-high`:
the real inverse transform has the exact multiplier at frequency `2πk / R`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace JanetCartan

variable {n : ℕ}

/-- `main:eq:smoothing-high`: evenness of the fixed real symbol makes its inverse
Fourier transform real. -/
theorem conj_cutoffComplexSchwartzKernel (y : EuclideanSpace ℝ (Fin n)) :
    conj (cutoffComplexSchwartzKernel n y) = cutoffComplexSchwartzKernel n y := by
  change conj (𝓕⁻ (cutoffComplexSchwartzSymbol n) y) = 𝓕⁻ (cutoffComplexSchwartzSymbol n) y
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_conj, ← integral_neg_eq_self (fun v : EuclideanSpace ℝ (Fin n) ↦
    (Real.fourierChar ⟪v, y⟫ : ℂ) * cutoffComplexSchwartzSymbol n v) volume]
  apply integral_congr_ae
  filter_upwards [] with v
  simp [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

/-- `main:eq:smoothing-high`: taking real parts does not change the kernel. -/
theorem ofReal_cutoffSchwartzKernel (y : EuclideanSpace ℝ (Fin n)) :
    (cutoffSchwartzKernel n y : ℂ) = cutoffComplexSchwartzKernel n y :=
  Complex.conj_eq_iff_re.mp (conj_cutoffComplexSchwartzKernel y)

/-- `main:eq:smoothing-high`: the actual real kernel has the prescribed Fourier
transform, including Mathlib's `2π` convention. -/
theorem integral_cutoffSchwartzKernel_fourierChar (ξ : EuclideanSpace ℝ (Fin n)) :
    (∫ y, (cutoffSchwartzKernel n y : ℂ) * (Real.fourierChar (-⟪y, ξ⟫) : ℂ)) =
      (fourierCutoff ξ : ℂ) := by
  have h := congrArg (fun g ↦ g ξ) (fourier_cutoffComplexSchwartzKernel n)
  simpa only [SchwartzMap.fourier_coe, Real.fourier_eq, Circle.smul_def,
    smul_eq_mul, ofReal_cutoffSchwartzKernel, mul_comm,
    cutoffComplexSchwartzSymbol_apply] using h

/-- `app:not:fourier`, `main:lem:smoothing`: the unit-torus character is the
Euclidean Fourier character at the integer lattice vector. -/
theorem mFourier_torusQuotient_eq_fourierChar (k : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (torusQuotient x) =
      (Real.fourierChar ⟪x, WithLp.toLp 2 (fun i ↦ (k i : ℝ))⟫ : ℂ) := by
  change (∏ i, fourier (k i) (x i : AddCircle (1 : ℝ))) = _
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_ofNat]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- `main:eq:smoothing-high`: translation and scaling of a character gives the
Fourier phase at exactly `(2π / R) k`. -/
theorem periodicLift_mFourier_sub_smul (k : Fin n → ℤ) (a : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    periodicLift (UnitAddTorus.mFourier k) (x - a • y) =
      periodicLift (UnitAddTorus.mFourier k) x *
        (Real.fourierChar (-⟪y, a • WithLp.toLp 2 (fun i ↦ (k i : ℝ))⟫) : ℂ) := by
  simp only [periodicLift, Function.comp_apply, mFourier_torusQuotient_eq_fourierChar,
    inner_sub_left, real_inner_smul_left, inner_smul_right]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- `main:eq:smoothing-high`: the Euclidean convolution acts on every character
by the exact fixed periodic cutoff symbol. -/
theorem integral_cutoffSchwartzKernel_mFourier (R : ℝ) (k : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y, (cutoffSchwartzKernel n y : ℂ) *
      periodicLift (UnitAddTorus.mFourier k) (x - (2 * Real.pi / R) • y)) =
      (periodicCutoffSymbol R k : ℂ) * periodicLift (UnitAddTorus.mFourier k) x := by
  simp_rw [periodicLift_mFourier_sub_smul, mul_left_comm _
    (periodicLift (UnitAddTorus.mFourier k) x)]
  rw [integral_const_mul, integral_cutoffSchwartzKernel_fourierChar]
  exact mul_comm _ _

end JanetCartan
