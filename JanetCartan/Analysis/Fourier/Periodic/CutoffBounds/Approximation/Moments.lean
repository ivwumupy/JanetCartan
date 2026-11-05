module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Integral

/-!
# Polynomial cancellation for the fixed cutoff kernel

For `main:lem:smoothing` and `main:eq:smoothing-high`, the fixed cutoff is constant
near zero, so all its positive derivatives vanish there. Fourier differentiation
therefore gives cancellation of products of inner products against its inverse
transform. Taking real parts and expanding in the Euclidean orthonormal basis
proves cancellation for arbitrary continuous multilinear maps with values in a
real Banach space. Consequently, integration against the fixed kernel reproduces
the constant term of every Taylor polynomial of positive length, at every real scale.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace JanetCartan

/-- `main:eq:smoothing-high`: Fourier differentiation at zero makes every positive
product of inner products cancel against the complex inverse transform. -/
theorem integral_prod_inner_smul_cutoffComplexSchwartzKernel_eq_zero (n j : ℕ)
    (hj : j ≠ 0) (m : Fin j → EuclideanSpace ℝ (Fin n)) :
    (∫ y, (∏ i, inner ℝ y (m i) : ℝ) • cutoffComplexSchwartzKernel n y) = 0 := by
  have hF : 𝓕 (cutoffComplexSchwartzKernel n : EuclideanSpace ℝ (Fin n) → ℂ) =
      (cutoffComplexSchwartzSymbol n : EuclideanSpace ℝ (Fin n) → ℂ) := by
    rw [← SchwartzMap.fourier_coe, fourier_cutoffComplexSchwartzKernel]
  have hd := Real.iteratedFDeriv_fourier (N := ⊤)
    (fun k _ ↦ (cutoffComplexSchwartzKernel n).integrable_pow_mul volume k)
    (cutoffComplexSchwartzKernel n).integrable.aestronglyMeasurable (n := j) le_top
  rw [hF] at hd
  have hi := VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
    ((cutoffComplexSchwartzKernel n).integrable_pow_mul volume j)
    (cutoffComplexSchwartzKernel n).integrable.aestronglyMeasurable
  have h := congrArg (fun f ↦ f 0 m) hd
  rw [iteratedFDeriv_cutoffComplexSchwartzSymbol_zero n j hj] at h
  rw [Real.fourier_continuousMultilinearMap_apply hi] at h
  simp only [zero_apply, Real.fourier_eq, inner_zero_right, neg_zero,
    AddChar.map_zero_eq_one, one_smul, VectorFourier.fourierPowSMulRight_apply,
    innerSL_apply_apply ℝ] at h
  rw [integral_smul] at h
  have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ j ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- `main:eq:smoothing-high`: products of inner products are integrable against
the complex kernel, by the weighted integrability used for Fourier differentiation. -/
theorem integrable_prod_inner_smul_cutoffComplexSchwartzKernel (n j : ℕ)
    (m : Fin j → EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ (∏ i, inner ℝ y (m i) : ℝ) • cutoffComplexSchwartzKernel n y) := by
  have hi := VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
    ((cutoffComplexSchwartzKernel n).integrable_pow_mul volume j)
    (cutoffComplexSchwartzKernel n).integrable.aestronglyMeasurable
  have he := (ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) ℂ m).integrable_comp hi
  simp only [ContinuousMultilinearMap.apply_apply,
    VectorFourier.fourierPowSMulRight_apply, innerSL_apply_apply ℝ] at he
  have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ j ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact (integrable_fun_smul_iff hc _).mp he

/-- `main:eq:smoothing-high`: taking real parts preserves cancellation of every
positive product of inner products. -/
theorem integral_cutoffSchwartzKernel_mul_prod_inner_eq_zero (n j : ℕ) (hj : j ≠ 0)
    (m : Fin j → EuclideanSpace ℝ (Fin n)) :
    (∫ y, cutoffSchwartzKernel n y * (∏ i, inner ℝ y (m i))) = 0 := by
  have h := congrArg Complex.reCLM
    (integral_prod_inner_smul_cutoffComplexSchwartzKernel_eq_zero n j hj m)
  rw [← Complex.reCLM.integral_comp_comm
    (integrable_prod_inner_smul_cutoffComplexSchwartzKernel n j m)] at h
  simpa only [map_smul, Complex.reCLM_apply, smul_eq_mul, map_zero,
    cutoffSchwartzKernel_apply, mul_comm] using h

/-- `main:eq:smoothing-high`: products of inner products are integrable against
the real cutoff kernel. -/
theorem integrable_cutoffSchwartzKernel_mul_prod_inner (n j : ℕ)
    (m : Fin j → EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y ↦ cutoffSchwartzKernel n y * (∏ i, inner ℝ y (m i))) := by
  simpa only [map_smul, Complex.reCLM_apply, smul_eq_mul, map_zero,
    cutoffSchwartzKernel_apply, mul_comm] using
    Complex.reCLM.integrable_comp (integrable_prod_inner_smul_cutoffComplexSchwartzKernel n j m)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `main:eq:smoothing-high`: every positive homogeneous multilinear moment of
the fixed real kernel vanishes, also for arbitrary real Banach-space coefficients. -/
theorem integral_cutoffSchwartzKernel_smul_multilinear_eq_zero (j : ℕ) (hj : j ≠ 0)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F) :
    (∫ y, cutoffSchwartzKernel n y • A (fun _ ↦ y)) = 0 := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hexp (y : EuclideanSpace ℝ (Fin n)) :
      A (fun _ ↦ y) = ∑ r : Fin j → Fin n,
        (∏ i, inner ℝ y (b (r i))) • A (fun i ↦ b (r i)) := by
    calc
      _ = A (fun _ ↦ ∑ i, b.repr y i • b i) := by
        congr 1
        funext _
        exact (b.sum_repr y).symm
      _ = _ := by
        rw [A.map_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [A.map_smul_univ]
        congr 2
        funext i
        simp only [b, EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_repr]
  simp_rw [hexp, Finset.smul_sum, smul_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro r _
    rw [integral_smul_const, integral_cutoffSchwartzKernel_mul_prod_inner_eq_zero n j hj, zero_smul]
  · intro r _
    exact (integrable_cutoffSchwartzKernel_mul_prod_inner n j (fun i ↦ b (r i))).smul_const _

/-- `main:eq:smoothing-high`: homogeneous moment cancellation holds at every
real displacement scale, including zero and negative scales. -/
theorem integral_cutoffSchwartzKernel_smul_multilinear_scaled_eq_zero (j : ℕ) (hj : j ≠ 0)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n)) F)
    (a : ℝ) :
    (∫ y, cutoffSchwartzKernel n y • A (fun _ ↦ a • y)) = 0 := by
  simp_rw [A.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_comm (cutoffSchwartzKernel n _)]
  rw [integral_smul, integral_cutoffSchwartzKernel_smul_multilinear_eq_zero j hj A, smul_zero]

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: integration against the fixed
kernel reproduces the constant term of a Taylor polynomial of positive length.
No regularity assumption on `g` is required for this finite polynomial identity. -/
theorem integral_cutoffSchwartzKernel_smul_taylor (g : EuclideanSpace ℝ (Fin n) → F)
    (N : ℕ) (hN : 0 < N) (x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    (∫ y, cutoffSchwartzKernel n y • cutoffTaylorPolynomial g N x (a • y)) = g x := by
  simp only [cutoffTaylorPolynomial, Finset.smul_sum, smul_comm (cutoffSchwartzKernel n _)]
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single 0]
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        iteratedFDeriv_zero_apply, integral_smul_const, integral_cutoffSchwartzKernel]
    · intro j _ hj
      rw [integral_smul, integral_cutoffSchwartzKernel_smul_multilinear_scaled_eq_zero j hj, smul_zero]
    · simp [hN]
  · intro j _
    exact (integrable_cutoffSchwartzKernel_smul_multilinear j (iteratedFDeriv ℝ j g x) a).smul _

end JanetCartan
