module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Basic

/-!
# Fourier coefficients of periodic weak derivatives

Testing the genuine distributional identity against the real and imaginary
Fourier characters gives the derivative symbol from `app:not:fourier`.
The squared coefficient identity and summability then give the converse
Sobolev membership implication used in the integer induction of
`app:ch_background:prop:bg-inverse`. All dimensions, including zero, and
arbitrary finite-dimensional real Hilbert targets are allowed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private lemma hasDerivAt_fourierCharacter_coordinate (k : Fin n → ℤ) (i : Fin n) (x : Torus n) :
    HasDerivAt (fun t : ℝ ↦ UnitAddTorus.mFourier k
      (x + Pi.single i (t : AddCircle (1 : ℝ))))
      (UnitAddTorus.mFourier k x * (2 * Real.pi * Complex.I * (k i : ℂ))) 0 := by
  classical
  have hsingle (t : ℝ) :
      UnitAddTorus.mFourier k (Pi.single i (t : AddCircle (1 : ℝ))) =
      fourier (k i) (t : AddCircle (1 : ℝ)) := by
    change (∏ j, fourier (k j) (((Pi.single i (t : AddCircle (1 : ℝ))) : Torus n) j)) = _
    rw [Finset.prod_eq_single i]
    · simp only [Pi.single_eq_same]
    · intro j _ hj
      simp only [Pi.single_eq_of_ne hj, fourier_eval_zero]
    · simp
  simpa only [periodicFourierCharacter_add, hsingle, AddCircle.coe_zero,
    fourier_eval_zero, Complex.ofReal_one, div_one, mul_one] using
    (hasDerivAt_fourier 1 (k i) 0).const_mul (UnitAddTorus.mFourier k x)

omit [FiniteDimensional ℝ F] in
private lemma periodicCoordinateDeriv_fourierRe_test (k : Fin n → ℤ) (i : Fin n) (a : F) :
    periodicCoordinateDeriv i (fun x ↦ (UnitAddTorus.mFourier k x).re • a) =
      fun x ↦ (-(2 * Real.pi * (k i : ℝ)) * (UnitAddTorus.mFourier k x).im) • a := by
  funext x
  have h := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_fourierCharacter_coordinate k i x)).smul_const a).deriv
  simpa [periodicCoordinateDeriv, Function.comp_def, Complex.mul_re, Complex.mul_im,
    mul_comm, mul_left_comm, mul_assoc] using h

omit [FiniteDimensional ℝ F] in
private lemma periodicCoordinateDeriv_fourierIm_test (k : Fin n → ℤ) (i : Fin n) (a : F) :
    periodicCoordinateDeriv i (fun x ↦ (UnitAddTorus.mFourier k x).im • a) =
      fun x ↦ ((2 * Real.pi * (k i : ℝ)) * (UnitAddTorus.mFourier k x).re) • a := by
  funext x
  have h := ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_fourierCharacter_coordinate k i x)).smul_const a).deriv
  simpa [periodicCoordinateDeriv, Function.comp_def, Complex.mul_re, Complex.mul_im,
    mul_comm, mul_left_comm, mul_assoc] using h

omit [FiniteDimensional ℝ F] in
private lemma isSmoothPeriodic_fourierRe_test (k : Fin n → ℤ) (a : F) :
    IsSmoothPeriodic (fun x ↦ (UnitAddTorus.mFourier k x).re • a) := by
  have h := isSmoothPeriodic_periodicFourierMode k (a, (0 : F))
  change IsSmoothPeriodic (fun x ↦ (UnitAddTorus.mFourier k x).re • a -
    (UnitAddTorus.mFourier k x).im • (0 : F)) at h
  simpa only [smul_zero, sub_zero] using h

omit [FiniteDimensional ℝ F] in
private lemma isSmoothPeriodic_fourierIm_test (k : Fin n → ℤ) (a : F) :
    IsSmoothPeriodic (fun x ↦ (UnitAddTorus.mFourier k x).im • a) := by
  have h := isSmoothPeriodic_periodicFourierMode k ((0 : F), -a)
  change IsSmoothPeriodic (fun x ↦ (UnitAddTorus.mFourier k x).re • (0 : F) -
    (UnitAddTorus.mFourier k x).im • (-a)) at h
  simpa only [smul_zero, smul_neg, zero_sub, neg_neg] using h

private lemma integral_inner_fourierRe_test (u : PeriodicL2 n F) (k : Fin n → ℤ) (a : F) :
    (∫ x, ⟪u x, (UnitAddTorus.mFourier (-k) x).re • a⟫) =
      ⟪a, (periodicFourierCoeff u k).1⟫ := by
  have h := congrArg Prod.fst (periodicFourierCoeff_inner (Lp.memLp u) a k)
  simpa only [periodicFourierCoeff, real_inner_smul_right, smul_eq_mul,
    real_inner_comm a] using h

private lemma integral_inner_fourierIm_test (u : PeriodicL2 n F) (k : Fin n → ℤ) (a : F) :
    (∫ x, ⟪u x, (UnitAddTorus.mFourier (-k) x).im • a⟫) =
      ⟪a, (periodicFourierCoeff u k).2⟫ := by
  have h := congrArg Prod.snd (periodicFourierCoeff_inner (Lp.memLp u) a k)
  simpa only [periodicFourierCoeff, real_inner_smul_right, smul_eq_mul,
    real_inner_comm a] using h

/-- The Fourier coefficient of an arbitrary periodic weak derivative is the
rotation by `2π kᵢ` from `app:not:fourier`. The identity follows by testing
against Fourier characters times arbitrary target vectors
(`app:ch_background:prop:bg-inverse`). -/
theorem HasPeriodicWeakDerivative.periodicFourierCoeff_eq {i : Fin n}
    {u v : PeriodicL2 n F} (h : HasPeriodicWeakDerivative i u v) (k : Fin n → ℤ) :
    periodicFourierCoeff v k =
      (-(2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff u k).2,
        (2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff u k).1) := by
  apply Prod.ext
  · apply ext_inner_left ℝ
    intro a
    have ht := h _ (isSmoothPeriodic_fourierRe_test (-k) a)
    rw [periodicCoordinateDeriv_fourierRe_test] at ht
    rw [← integral_inner_fourierRe_test v k a, real_inner_smul_right, neg_mul,
      ← integral_inner_fourierIm_test u k a]
    simpa [Pi.neg_apply, real_inner_smul_right, mul_assoc, integral_const_mul] using ht
  · apply ext_inner_left ℝ
    intro a
    have ht := h _ (isSmoothPeriodic_fourierIm_test (-k) a)
    rw [periodicCoordinateDeriv_fourierIm_test] at ht
    rw [← integral_inner_fourierIm_test v k a, real_inner_smul_right,
      ← integral_inner_fourierRe_test u k a]
    simpa [Pi.neg_apply, real_inner_smul_right, mul_assoc, integral_const_mul, integral_neg] using ht

/-- Weak coordinate differentiation multiplies the squared real-pair Fourier
energy by `(2π kᵢ)²` (`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem HasPeriodicWeakDerivative.sq_periodicFourierCoeff {i : Fin n}
    {u v : PeriodicL2 n F} (h : HasPeriodicWeakDerivative i u v) (k : Fin n → ℤ) :
    ‖(periodicFourierCoeff v k).1‖ ^ 2 + ‖(periodicFourierCoeff v k).2‖ ^ 2 =
      (2 * Real.pi * (k i : ℝ)) ^ 2 *
        (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2) := by
  rw [h.periodicFourierCoeff_eq]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
  ring

/-- An L² field in level `s` whose coordinate weak derivatives are all in
level `s` belongs to level `s + 1` (`app:ch_background:prop:bg-inverse`).
This uses the sum of the convergent coefficient-energy series and the exact
identity `frequencyNorm_sq_eq_sum`, also when the coordinate sum is empty. -/
theorem mem_periodicSobolevLevel_succ_of_weakDerivatives {s : ℕ}
    {u : PeriodicL2 n F} {v : Fin n → PeriodicL2 n F}
    (hu : u ∈ periodicSobolevLevel n F s)
    (hv : ∀ i, v i ∈ periodicSobolevLevel n F s)
    (hd : ∀ i, HasPeriodicWeakDerivative i u (v i)) :
    u ∈ periodicSobolevLevel n F (s + 1) := by
  rw [mem_periodicSobolevLevel_iff] at hu ⊢
  have hv' := fun i ↦ (mem_periodicSobolevLevel_iff s (v i)).mp (hv i)
  refine (hu.add (summable_sum (s := Finset.univ) (fun i _ ↦ hv' i))).congr ?_
  intro k
  simp only [Real.rpow_natCast, (hd _).sq_periodicFourierCoeff]
  rw [pow_succ (1 + frequencyNorm k ^ 2) s]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← frequencyNorm_sq_eq_sum]
  ring

end JanetCartan
