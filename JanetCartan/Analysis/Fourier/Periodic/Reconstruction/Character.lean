module

public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivative bounds for individual Fourier modes

The physical frequency convention of `paper.tex`, `app:not:fourier`, gives the
operator norm bound `frequencyNorm k ^ j` for derivatives of each sine and cosine.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace ContDiff

namespace JanetCartan

variable {n : ℕ}

/-- The phase functional of a unit-torus character (`app:not:fourier`). -/
def periodicFourierPhase (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (2 * Real.pi) • innerSL ℝ (WithLp.toLp 2 (fun i ↦ (k i : ℝ)))

/-- Its operator norm is exactly the physical frequency (`app:not:fourier`). -/
theorem norm_periodicFourierPhase (k : Fin n → ℤ) :
    ‖periodicFourierPhase k‖ = frequencyNorm k := by
  simp [periodicFourierPhase, norm_smul, innerSL_apply_norm, frequencyNorm,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Fourier characters on the Euclidean lift are exponentials of their phase
(`app:not:fourier`). -/
theorem mFourier_torusQuotient_eq_exp (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (torusQuotient x) =
      Complex.exp ((periodicFourierPhase k x : ℂ) * Complex.I) := by
  change (∏ i, fourier (k i) (x i : AddCircle (1 : ℝ))) = _
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [periodicFourierPhase, smul_apply, innerSL_apply_apply,
    smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_ofNat]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- The real mode on Euclidean space is the expected sine-cosine combination
(`app:not:fourier`). -/
theorem periodicLift_periodicFourierMode {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : Fin n → ℤ) (a b : F) :
    periodicLift (periodicFourierModeOfParts k a b) =
      fun x ↦ Real.cos (periodicFourierPhase k x) • a -
        Real.sin (periodicFourierPhase k x) • b := by
  funext x
  simp [periodicLift, periodicFourierModeOfParts, periodicFourierMode, mFourier_torusQuotient_eq_exp,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Every individual real Fourier mode is smooth (`app:not:fourier`). -/
theorem contDiff_periodicLift_periodicFourierMode {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : Fin n → ℤ) (a b : F) :
    ContDiff ℝ ∞ (periodicLift (periodicFourierModeOfParts k a b)) := by
  rw [periodicLift_periodicFourierMode]
  exact ((Real.contDiff_cos.comp (periodicFourierPhase k).contDiff).smul contDiff_const).sub
    ((Real.contDiff_sin.comp (periodicFourierPhase k).contDiff).smul contDiff_const)

private theorem norm_iteratedFDeriv_trig_phase_le (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hb : ∀ j y, ‖iteratedDeriv j g y‖ ≤ 1)
    (k : Fin n → ℤ) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (g ∘ periodicFourierPhase k) x‖ ≤ frequencyNorm k ^ j := by
  rw [(periodicFourierPhase k).iteratedFDeriv_comp_right hg x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j g (periodicFourierPhase k x)‖ *
        ∏ _ : Fin j, ‖periodicFourierPhase k‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * frequencyNorm k ^ j := by
      simp only [norm_periodicFourierPhase, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact mul_le_mul_of_nonneg_right (hb j _) (pow_nonneg (by
        unfold frequencyNorm; positivity) j)
    _ = _ := one_mul _

/-- Each derivative of a cosine mode has the physical frequency power bound
(`app:lem:sharp-fourier-embedding`). -/
theorem norm_iteratedFDeriv_cos_periodicFourierPhase_le (k : Fin n → ℤ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (Real.cos ∘ periodicFourierPhase k) x‖ ≤ frequencyNorm k ^ j :=
  norm_iteratedFDeriv_trig_phase_le Real.cos Real.contDiff_cos
    (fun j y ↦ Real.abs_iteratedDeriv_cos_le_one j y) k j x

/-- Each derivative of a sine mode has the physical frequency power bound
(`app:lem:sharp-fourier-embedding`). -/
theorem norm_iteratedFDeriv_sin_periodicFourierPhase_le (k : Fin n → ℤ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (Real.sin ∘ periodicFourierPhase k) x‖ ≤ frequencyNorm k ^ j :=
  norm_iteratedFDeriv_trig_phase_le Real.sin Real.contDiff_sin
    (fun j y ↦ Real.abs_iteratedDeriv_sin_le_one j y) k j x

/-- Operator norms of all derivatives of one real Fourier mode
(`app:lem:sharp-fourier-embedding`). -/
theorem norm_iteratedFDeriv_periodicFourierMode_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : Fin n → ℤ) (a b : F) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift (periodicFourierModeOfParts k a b)) x‖ ≤
      frequencyNorm k ^ j * (‖a‖ + ‖b‖) := by
  have hc : ContDiff ℝ (j : WithTop ℕ∞) (Real.cos ∘ periodicFourierPhase k) :=
    Real.contDiff_cos.comp (periodicFourierPhase k).contDiff
  have hs : ContDiff ℝ (j : WithTop ℕ∞) (Real.sin ∘ periodicFourierPhase k) :=
    Real.contDiff_sin.comp (periodicFourierPhase k).contDiff
  have hca : ContDiff ℝ (j : WithTop ℕ∞)
      (fun x ↦ Real.cos (periodicFourierPhase k x) • a) := hc.smul contDiff_const
  have hsb : ContDiff ℝ (j : WithTop ℕ∞)
      (fun x ↦ Real.sin (periodicFourierPhase k x) • b) := hs.smul contDiff_const
  rw [periodicLift_periodicFourierMode]
  change ‖iteratedFDeriv ℝ j ((fun x ↦ Real.cos (periodicFourierPhase k x) • a) -
    (fun x ↦ Real.sin (periodicFourierPhase k x) • b)) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply hca.contDiffAt hsb.contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun x ↦ Real.cos (periodicFourierPhase k x) • a) x‖ +
        ‖iteratedFDeriv ℝ j (fun x ↦ Real.sin (periodicFourierPhase k x) • b) x‖ :=
      norm_sub_le _ _
    _ ≤ ‖a‖ * frequencyNorm k ^ j + ‖b‖ * frequencyNorm k ^ j := by
      apply add_le_add
      · calc
          _ ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight a‖ *
              ‖iteratedFDeriv ℝ j (Real.cos ∘ periodicFourierPhase k) x‖ :=
            ((ContinuousLinearMap.id ℝ ℝ).smulRight a).norm_iteratedFDeriv_comp_left
              hc.contDiffAt le_rfl
          _ ≤ _ := by
            simp only [ContinuousLinearMap.norm_smulRight_apply,
              ContinuousLinearMap.norm_id, one_mul]
            exact mul_le_mul_of_nonneg_left
              (norm_iteratedFDeriv_cos_periodicFourierPhase_le k j x) (norm_nonneg a)
      · calc
          _ ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight b‖ *
              ‖iteratedFDeriv ℝ j (Real.sin ∘ periodicFourierPhase k) x‖ :=
            ((ContinuousLinearMap.id ℝ ℝ).smulRight b).norm_iteratedFDeriv_comp_left
              hs.contDiffAt le_rfl
          _ ≤ _ := by
            simp only [ContinuousLinearMap.norm_smulRight_apply,
              ContinuousLinearMap.norm_id, one_mul]
            exact mul_le_mul_of_nonneg_left
              (norm_iteratedFDeriv_sin_periodicFourierPhase_le k j x) (norm_nonneg b)
    _ = _ := by ring

end JanetCartan
