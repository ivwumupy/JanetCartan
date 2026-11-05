module

public import JanetCartan.Analysis.Fourier.Periodic.Interpolation
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev

/-!
# Sobolev tails for the finite-stage cutoff

The final cutoff paragraph of `main:thm:step` uses the same `periodicCutoff`
as the increment. Its plateau and multiplier identity give the loss of `k`
Sobolev orders with gain `R⁻ᵏ`. These are inputs to the profile estimates for
`FiniteStage.correction_of_component_estimates`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiniteStage

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem coeff_sub {f g : Torus n → F} (hf : Continuous f) (hg : Continuous g)
    (l : Fin n → ℤ) :
    periodicFourierCoeff (f - g) l = periodicFourierCoeff f l - periodicFourierCoeff g l := by
  have hi (a : Torus n → ℝ) (ha : Continuous a) {u : Torus n → F} (hu : Continuous u) :
      MeasureTheory.Integrable (fun x ↦ a x • u x) :=
    (ha.smul hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext <;> simp only [periodicFourierCoeff, Pi.sub_apply, smul_sub, Prod.fst_sub,
    Prod.snd_sub] <;> apply MeasureTheory.integral_sub
  · exact hi _ (Complex.continuous_re.comp (UnitAddTorus.mFourier (-l)).continuous) hf
  · exact hi _ (Complex.continuous_re.comp (UnitAddTorus.mFourier (-l)).continuous) hg
  · exact hi _ (Complex.continuous_im.comp (UnitAddTorus.mFourier (-l)).continuous) hf
  · exact hi _ (Complex.continuous_im.comp (UnitAddTorus.mFourier (-l)).continuous) hg

omit [FiniteDimensional ℝ F] in
/-- The final cutoff in `main:thm:step` has a smooth tail, for the actual input field. -/
theorem smooth_cutoffTail {f : Torus n → F} (hf : IsSmoothPeriodic f) (R : ℝ) :
    IsSmoothPeriodic (f - periodicCutoff R f) :=
  ⟨hf.1.sub (isSmoothPeriodic_periodicCutoff R f).1,
    hf.2.sub (isSmoothPeriodic_periodicCutoff R f).2⟩

/-- The spectral-tail estimate in the final paragraph of `main:thm:step`.
Only the input Sobolev norm of order `s+k` occurs, and the operator is the
fixed real-even cutoff used in `FiniteStage.increment`. -/
theorem sobolev_cutoffTail_le {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {R : ℝ} (hR : 0 < R) (s k : ℕ) :
    periodicSobolevNorm s (f - periodicCutoff R f) ≤
      (R ^ k)⁻¹ * periodicSobolevNorm (s + k : ℕ) f := by
  have hcoeff (l : Fin n → ℤ) :
      periodicFourierCoeff (f - periodicCutoff R f) l =
        (1 - periodicCutoffSymbol R l) • periodicFourierCoeff f l := by
    rw [coeff_sub hf.1 (isSmoothPeriodic_periodicCutoff R f).1,
      periodicFourierCoeff_periodicCutoff hf.1 hR, sub_smul, one_smul]
  have hterm (l : Fin n → ℤ) :
      (1 + frequencyNorm l ^ 2) ^ s *
        (‖(periodicFourierCoeff (f - periodicCutoff R f) l).1‖ ^ 2 +
          ‖(periodicFourierCoeff (f - periodicCutoff R f) l).2‖ ^ 2) ≤
      ((R ^ k)⁻¹) ^ 2 * ((1 + frequencyNorm l ^ 2) ^ (s + k) *
        (‖(periodicFourierCoeff f l).1‖ ^ 2 + ‖(periodicFourierCoeff f l).2‖ ^ 2)) := by
    rw [hcoeff]
    by_cases hl : frequencyNorm l ≤ R
    · simp only [periodicCutoffSymbol_eq_one hR hl, sub_self, zero_smul,
        Prod.fst_zero, Prod.snd_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
        zero_add, mul_zero]
      positivity
    have hsymbol := fourierCutoff_mem_Icc
      ((2 * Real.pi / R) •
        (WithLp.toLp 2 (fun i ↦ (l i : ℝ)) : EuclideanSpace ℝ (Fin n)))
    change 0 ≤ periodicCutoffSymbol R l ∧ periodicCutoffSymbol R l ≤ 1 at hsymbol
    have ha : |1 - periodicCutoffSymbol R l| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hsq := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hw : (R ^ k) ^ 2 ≤ (1 + frequencyNorm l ^ 2) ^ k := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      apply pow_le_pow_left₀ (sq_nonneg R)
      nlinarith [lt_of_not_ge hl]
    have hinv : ((R ^ k)⁻¹) ^ 2 * (R ^ k) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt (pow_pos hR k)), one_pow]
    have hw' : 1 ≤ ((R ^ k)⁻¹) ^ 2 * (1 + frequencyNorm l ^ 2) ^ k := by
      simpa only [hinv] using mul_le_mul_of_nonneg_left hw (sq_nonneg ((R ^ k)⁻¹))
    simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs, mul_pow]
    have he : 0 ≤ ‖(periodicFourierCoeff f l).1‖ ^ 2 +
        ‖(periodicFourierCoeff f l).2‖ ^ 2 := by positivity
    calc
      _ = (1 + frequencyNorm l ^ 2) ^ s *
          (|1 - periodicCutoffSymbol R l| ^ 2 *
            (‖(periodicFourierCoeff f l).1‖ ^ 2 + ‖(periodicFourierCoeff f l).2‖ ^ 2)) := by ring
      _ ≤ (1 + frequencyNorm l ^ 2) ^ s *
          (1 * (‖(periodicFourierCoeff f l).1‖ ^ 2 + ‖(periodicFourierCoeff f l).2‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by simpa using hsq) he)
          (by positivity)
      _ ≤ (1 + frequencyNorm l ^ 2) ^ s *
          ((((R ^ k)⁻¹) ^ 2 * (1 + frequencyNorm l ^ 2) ^ k) *
            (‖(periodicFourierCoeff f l).1‖ ^ 2 + ‖(periodicFourierCoeff f l).2‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw' he) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hs := (smooth_cutoffTail hf R).summable_periodicSobolevNorm s
  have ht := hf.summable_periodicSobolevNorm (s + k)
  simp only [Real.rpow_natCast] at hs ht
  have hsum := hs.tsum_le_tsum hterm (ht.mul_left (((R ^ k)⁻¹) ^ 2))
  unfold periodicSobolevNorm
  simp only [Real.rpow_natCast]
  apply (Real.sqrt_le_sqrt hsum).trans_eq
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

end JanetCartan.FiniteStage
