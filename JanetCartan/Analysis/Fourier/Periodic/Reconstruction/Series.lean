module

public import JanetCartan.Analysis.Fourier.Periodic.Deriv
public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic

/-!
# Reconstruction from real Fourier coefficient pairs

Pointwise Fourier inversion in the convention of `paper.tex`, `app:not:fourier`.
The convergence statements establish summability before using a totalized sum.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reconstruction with separate coefficient components agrees with the shared
pair-taking cutoff mode in the convention of `app:not:fourier`. -/
theorem periodicFourierModeOfParts_eq_periodicFourierMode
    (k : Fin n → ℤ) (a b : F) :
    periodicFourierModeOfParts k a b = periodicFourierMode k (a, b) := rfl

omit [NormedSpace ℝ F] in
/-- The elementary two-component estimate used in `app:lem:sharp-fourier-embedding`. -/
theorem norm_add_norm_le_sqrt_two_mul (a b : F) :
    ‖a‖ + ‖b‖ ≤ Real.sqrt 2 * Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h₂ := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h := Real.sq_sqrt (show 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 by positivity)
  have hp : 0 ≤ Real.sqrt 2 * Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by positivity
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ + ‖b‖ +
    Real.sqrt 2 * Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2))]

/-- A mode is bounded uniformly by the sum of the coefficient norms (`app:not:fourier`). -/
theorem norm_periodicFourierMode_le (k : Fin n → ℤ) (a b : F) (x : Torus n) :
    ‖periodicFourierModeOfParts k a b x‖ ≤ ‖a‖ + ‖b‖ := by
  have hr := Complex.abs_re_le_norm (UnitAddTorus.mFourier k x)
  have hi := Complex.abs_im_le_norm (UnitAddTorus.mFourier k x)
  rw [periodicFourierCharacter_norm] at hr hi
  calc
    _ ≤ ‖(UnitAddTorus.mFourier k x).re • a‖ +
        ‖(UnitAddTorus.mFourier k x).im • b‖ := norm_sub_le _ _
    _ ≤ _ := by
      simpa only [norm_smul, Real.norm_eq_abs, one_mul] using
        add_le_add (mul_le_mul_of_nonneg_right hr (norm_nonneg a))
        (mul_le_mul_of_nonneg_right hi (norm_nonneg b))

/-- Real scalar Fourier inversion, with absolute convergence (`app:not:fourier`). -/
theorem hasSum_periodicFourierMode_real {f : Torus n → ℝ} (hf : Continuous f)
    (hs : Summable (fun k ↦ ‖(periodicFourierCoeff f k).1‖ +
      ‖(periodicFourierCoeff f k).2‖)) (x : Torus n) :
    HasSum (fun k ↦ periodicFourierModeOfParts k (periodicFourierCoeff f k).1
      (periodicFourierCoeff f k).2 x) (f x) := by
  let g : C(Torus n, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hc : Summable (UnitAddTorus.mFourierCoeff g) := by
    apply Summable.of_norm_bounded hs
    intro k
    rw [periodicFourierCoeff_eq_complex_parts hf]
    exact Complex.norm_le_abs_re_add_abs_im _
  have h := (Complex.reCLM.hasSum
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hc x))
  convert h using 1
  · funext k
    simp [periodicFourierModeOfParts, periodicFourierMode, periodicFourierCoeff_eq_complex_parts hf,
      Complex.mul_re, smul_eq_mul, mul_comm, g]
  · rfl

/-- Banach-valued Fourier inversion from summable real coefficient norms
(`app:not:fourier`). Separation by real continuous linear functionals reduces to
Mathlib's scalar Fourier inversion theorem. -/
theorem hasSum_periodicFourierMode [CompleteSpace F] {f : Torus n → F}
    (hf : Continuous f)
    (hs : Summable (fun k ↦ ‖(periodicFourierCoeff f k).1‖ +
      ‖(periodicFourierCoeff f k).2‖)) (x : Torus n) :
    HasSum (fun k ↦ periodicFourierModeOfParts k (periodicFourierCoeff f k).1
      (periodicFourierCoeff f k).2 x) (f x) := by
  have hm : Summable (fun k ↦ periodicFourierModeOfParts k (periodicFourierCoeff f k).1
      (periodicFourierCoeff f k).2 x) :=
    Summable.of_norm_bounded hs (fun k ↦ norm_periodicFourierMode_le k _ _ x)
  suffices heq : (∑' k, periodicFourierModeOfParts k (periodicFourierCoeff f k).1
      (periodicFourierCoeff f k).2 x) = f x by
    exact heq ▸ hm.hasSum
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hsL : Summable (fun k ↦ ‖(periodicFourierCoeff (fun y ↦ L (f y)) k).1‖ +
      ‖(periodicFourierCoeff (fun y ↦ L (f y)) k).2‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ (hs.mul_left ‖L‖)
    intro k
    rw [periodicFourierCoeff_map L hf, mul_add]
    exact add_le_add (L.le_opNorm _) (L.le_opNorm _)
  have h := hasSum_periodicFourierMode_real (f := fun y ↦ L (f y)) (L.continuous.comp hf) hsL x
  have hmL := L.hasSum hm.hasSum
  have he : (fun k ↦ periodicFourierModeOfParts k
      (periodicFourierCoeff (fun y ↦ L (f y)) k).1
      (periodicFourierCoeff (fun y ↦ L (f y)) k).2 x) =
      (fun k ↦ L (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
        (periodicFourierCoeff f k).2 x)) := by
    funext k
    simp only [periodicFourierCoeff_map L hf, periodicFourierModeOfParts, periodicFourierMode, map_sub, map_smul]
  rw [he] at h
  exact hmL.unique h

end JanetCartan
