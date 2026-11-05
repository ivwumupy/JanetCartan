module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivative bounds for real Fourier modes

The pointwise mode estimate for `main:eq:history-bernstein` and `main:eq:final-Cr`
in paper.tex. The Euclidean norm of the linear phase is precisely the physical
frequency, so each derivative contributes one frequency factor.
-/

@[expose] public noncomputable section

open scoped ContDiff RealInnerProductSpace

namespace JanetCartan.BernsteinL2

variable {n : ℕ}

/-- `app:not:fourier`: the real linear phase with the unit-torus factor `2π`. -/
def fourierPhaseCLM (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (2 * Real.pi) • innerSL ℝ (WithLp.toLp 2 (fun i ↦ (k i : ℝ)))

/-- `app:not:fourier`: coordinate formula for the physical linear phase. -/
lemma fourierPhaseCLM_apply (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    fourierPhaseCLM k x = 2 * Real.pi * ∑ i, (k i : ℝ) * x i := by
  simp [fourierPhaseCLM, PiLp.inner_apply, mul_comm]

/-- `main:eq:final-Cr`: the phase norm is exactly the physical frequency. -/
lemma norm_fourierPhaseCLM (k : Fin n → ℤ) : ‖fourierPhaseCLM k‖ = frequencyNorm k := by
  simp [fourierPhaseCLM, norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos, frequencyNorm]

/-- `app:not:fourier`: the lifted character is the exponential of its linear phase. -/
lemma periodicLift_mFourier_eq_exp (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    periodicLift (UnitAddTorus.mFourier k) x =
      Complex.exp ((fourierPhaseCLM k x : ℝ) * Complex.I) := by
  change (∏ i, fourier (k i) (x i : AddCircle (1 : ℝ))) = _
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [fourierPhaseCLM_apply]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `main:eq:final-Cr`: all scalar trigonometric derivatives have norm at most one. -/
lemma norm_iteratedDeriv_cos_sin_le_one (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j Real.cos t‖ ≤ 1 ∧ ‖iteratedDeriv j Real.sin t‖ ≤ 1 := by
  induction j with
  | zero => simpa using And.intro (Real.abs_cos_le_one t) (Real.abs_sin_le_one t)
  | succ j ih =>
    simpa only [Real.iteratedDeriv_add_one_cos, Real.iteratedDeriv_add_one_sin,
      Pi.neg_apply, norm_neg] using And.intro ih.2 ih.1

/-- `main:eq:final-Cr`: composition with the physical phase gives one frequency
factor per derivative. -/
lemma norm_iteratedFDeriv_comp_fourierPhase_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hbound : ∀ j t, ‖iteratedDeriv j g t‖ ≤ 1)
    (k : Fin n → ℤ) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (g ∘ fourierPhaseCLM k) x‖ ≤ frequencyNorm k ^ j := by
  rw [(fourierPhaseCLM k).iteratedFDeriv_comp_right hg x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (fourierPhaseCLM k x)‖ * ∏ _i : Fin j, ‖fourierPhaseCLM k‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * frequencyNorm k ^ j := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_fourierPhaseCLM,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact mul_le_mul_of_nonneg_right (hbound j _) (by unfold frequencyNorm; positivity)
    _ = _ := one_mul _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:final-Cr`: multiplication by a fixed vector in the mode estimate. -/
lemma norm_iteratedFDeriv_smul_const_le {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : F) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (fun x ↦ g x • a) x‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ j g x‖ := by
  change ‖iteratedFDeriv ℝ j ((ContinuousLinearMap.toSpanSingleton ℝ a) ∘ g) x‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hg.contDiffAt (by simp)]
  simpa using ContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (ContinuousLinearMap.toSpanSingleton ℝ a) (iteratedFDeriv ℝ j g x)

/-- `app:not:fourier`: cosine-sine representation of the shared real Fourier mode. -/
lemma periodicLift_fourierMode_eq_cos_sin (k : Fin n → ℤ) (a : F × F) :
    periodicLift (periodicFourierMode k a) = fun x ↦
      Real.cos (fourierPhaseCLM k x) • a.1 - Real.sin (fourierPhaseCLM k x) • a.2 := by
  funext x
  change (periodicLift (UnitAddTorus.mFourier k) x).re • a.1 -
    (periodicLift (UnitAddTorus.mFourier k) x).im • a.2 = _
  rw [periodicLift_mFourier_eq_exp, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero]

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: the sharp derivative bound
for a real Fourier mode. -/
lemma norm_iteratedFDeriv_periodicFourierMode_le (k : Fin n → ℤ) (a : F × F) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift (periodicFourierMode k a)) x‖ ≤
      frequencyNorm k ^ j * (‖a.1‖ + ‖a.2‖) := by
  have hc : ContDiff ℝ ∞ (Real.cos ∘ fourierPhaseCLM k) :=
    Real.contDiff_cos.comp (fourierPhaseCLM k).contDiff
  have hs : ContDiff ℝ ∞ (Real.sin ∘ fourierPhaseCLM k) :=
    Real.contDiff_sin.comp (fourierPhaseCLM k).contDiff
  rw [periodicLift_fourierMode_eq_cos_sin]
  change ‖iteratedFDeriv ℝ j ((fun x ↦ (Real.cos ∘ fourierPhaseCLM k) x • a.1) -
    (fun x ↦ (Real.sin ∘ fourierPhaseCLM k) x • a.2)) x‖ ≤ _
  rw [iteratedFDeriv_sub (f := fun x ↦ (Real.cos ∘ fourierPhaseCLM k) x • a.1)
    (g := fun x ↦ (Real.sin ∘ fourierPhaseCLM k) x • a.2)
    ((hc.smul contDiff_const).of_le (by simp))
    ((hs.smul contDiff_const).of_le (by simp)), Pi.sub_apply]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun x ↦ (Real.cos ∘ fourierPhaseCLM k) x • a.1) x‖ +
        ‖iteratedFDeriv ℝ j (fun x ↦ (Real.sin ∘ fourierPhaseCLM k) x • a.2) x‖ := norm_sub_le _ _
    _ ≤ ‖a.1‖ * ‖iteratedFDeriv ℝ j (Real.cos ∘ fourierPhaseCLM k) x‖ +
        ‖a.2‖ * ‖iteratedFDeriv ℝ j (Real.sin ∘ fourierPhaseCLM k) x‖ :=
      add_le_add (norm_iteratedFDeriv_smul_const_le hc _ _ _) (norm_iteratedFDeriv_smul_const_le hs _ _ _)
    _ ≤ ‖a.1‖ * frequencyNorm k ^ j + ‖a.2‖ * frequencyNorm k ^ j := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_comp_fourierPhase_le Real.contDiff_cos
            (fun j t ↦ (norm_iteratedDeriv_cos_sin_le_one j t).1) k j x) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_comp_fourierPhase_le Real.contDiff_sin
            (fun j t ↦ (norm_iteratedDeriv_cos_sin_le_one j t).2) k j x) (norm_nonneg _)
    _ = _ := by ring

end JanetCartan.BernsteinL2
