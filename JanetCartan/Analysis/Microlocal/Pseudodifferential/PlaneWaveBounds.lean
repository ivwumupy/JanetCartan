module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.SourceBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Composition

/-!
# Finite plane wave derivative bounds

The unit-frequency plane waves in `app:ch_regular_base:thm:actual-calculus`
contribute exactly one factor `2π ‖η‖` per source derivative.
-/

@[expose] public noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace JanetCartan.Pseudodifferential

/-- `app:ch_regular_base:thm:actual-calculus`: the scalar character's exact derivatives. -/
theorem iteratedDeriv_fourierChar (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ (Real.fourierChar t : ℂ)) =
      fun t ↦ (2 * Real.pi * Complex.I) ^ n * Real.fourierChar t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_const_mul_field, Real.deriv_fourierChar, pow_succ]
    ring

/-- `app:ch_regular_base:thm:actual-calculus`: smoothness of the scalar character. -/
theorem contDiff_fourierChar : ContDiff ℝ ∞ (fun t : ℝ ↦ (Real.fourierChar t : ℂ)) := by
  simp only [Real.fourierChar_apply]
  have ho : ContDiff ℝ ∞ (fun t : ℝ ↦ ((2 * Real.pi * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  fun_prop

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `app:ch_regular_base:thm:actual-calculus`: source derivatives of a plane wave,
with the manuscript convention converted to unit frequency. -/
theorem norm_iteratedFDeriv_planeWave_le (η y : V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z : V ↦ (Real.fourierChar ⟪η, z⟫ : ℂ)) y‖ ≤
      (2 * Real.pi * ‖η‖) ^ n := by
  have h := norm_iteratedFDeriv_comp_linear_le (innerSL ℝ η)
    (fun t : ℝ ↦ (Real.fourierChar t : ℂ)) contDiff_fourierChar n y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_fourierChar] at h
  simpa [Function.comp_def, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_pow] using h

/-- `app:ch_regular_base:thm:actual-calculus`: a uniform finite jet bound for
scalar multiplication, with the explicit Leibniz constant. -/
theorem norm_iteratedFDeriv_smul_le_uniform
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : V → ℂ) (g : V → F) (n j : ℕ) (hj : j ≤ n)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (y : V) (A B : ℝ)
    (hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f y‖ ≤ A)
    (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g y‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun z ↦ f z • g z) y‖ ≤ 2 ^ n * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply (norm_iteratedFDeriv_smul_le hf hg y (by exact_mod_cast hj)).trans
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact hA i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj)
      · exact hB (j - i) ((Nat.sub_le _ _).trans hj)
    _ = 2 ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := by
      gcongr
      norm_num
end JanetCartan.Pseudodifferential
