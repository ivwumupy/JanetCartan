module

public import JanetCartan.Analysis.Fourier.Periodic.Interpolation
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Scale
public import JanetCartan.Analysis.Iteration.FiniteAccuracy

/-!
# Sobolev profiles of the prepared residual

For `main:eq:actual-fine-source`, a Fourier energy split upgrades the unit L²
budget and the coarse high profiles to the fine scale `R`. Only actual smooth
fields on the shared torus are used, with its normalized Haar measure. There is
no identification of these fields with the Euclidean initial-data space.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

private theorem preparedResidual_split_weight {ρ R r m : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (hr : 0 ≤ r) (hrm : r ≤ m) :
    ρ ^ r ≤ (R ^ r) ^ 2 + (R ^ (r - m)) ^ 2 * ρ ^ m := by
  have hpow (s : ℝ) : (R ^ 2) ^ s = (R ^ s) ^ 2 := by
    calc
      (R ^ 2) ^ s = R ^ ((2 : ℝ) * s) := by rw [Real.rpow_mul hR.le, Real.rpow_two]
      _ = R ^ (s * 2) := by congr 1; ring
      _ = (R ^ s) ^ 2 := by rw [Real.rpow_mul hR.le, Real.rpow_two]
  by_cases h : ρ ≤ R ^ 2
  · calc
      _ ≤ (R ^ 2) ^ r := Real.rpow_le_rpow hρ.le h hr
      _ = (R ^ r) ^ 2 := hpow r
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hhigh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hR)
      (le_of_not_ge h) (sub_nonpos.mpr hrm)
    calc
      _ = ρ ^ (r - m) * ρ ^ m := by rw [← Real.rpow_add hρ, sub_add_cancel]
      _ ≤ (R ^ 2) ^ (r - m) * ρ ^ m :=
        mul_le_mul_of_nonneg_right hhigh (Real.rpow_nonneg hρ.le _)
      _ = (R ^ (r - m)) ^ 2 * ρ ^ m := by rw [hpow]
      _ ≤ _ := le_add_of_nonneg_left (sq_nonneg _)

/-- `main:eq:actual-fine-source`: split the Fourier energy at Bessel frequency `R`.
Smoothness supplies all summability and Parseval inputs. -/
theorem periodicSobolevNorm_le_preparedSource_split {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {f : Torus n → F} (hf : IsSmoothPeriodic f)
    {r m : ℕ} (hrm : r ≤ m) {R : ℝ} (hR : 0 < R) :
    periodicSobolevNorm r f ≤ R ^ (r : ℝ) * periodicL2Norm f +
      R ^ ((r : ℝ) - m) * periodicSobolevNorm m f := by
  let e := fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
    ‖(periodicFourierCoeff f k).2‖ ^ 2
  have he : Summable e := hf.hasSum_sq_periodicFourierCoeff.summable
  have hm := hf.summable_periodicSobolevNorm m
  have hs := (he.mul_left ((R ^ (r : ℝ)) ^ 2)).add
    (hm.mul_left ((R ^ ((r : ℝ) - m)) ^ 2))
  have hterm (k : Fin n → ℤ) :
      (1 + frequencyNorm k ^ 2) ^ (r : ℝ) * e k ≤
        (R ^ (r : ℝ)) ^ 2 * e k + (R ^ ((r : ℝ) - m)) ^ 2 *
          ((1 + frequencyNorm k ^ 2) ^ (m : ℝ) * e k) := by
    have := mul_le_mul_of_nonneg_right
      (preparedResidual_split_weight (ρ := 1 + frequencyNorm k ^ 2) (by positivity) hR
        (Nat.cast_nonneg r) (Nat.cast_le.mpr hrm)) (show 0 ≤ e k by dsimp [e]; positivity)
    simpa only [add_mul, mul_assoc] using this
  have hsum := (hf.summable_periodicSobolevNorm r).tsum_le_tsum hterm hs
  rw [(he.mul_left ((R ^ (r : ℝ)) ^ 2)).tsum_add
    (hm.mul_left ((R ^ ((r : ℝ) - m)) ^ 2))] at hsum
  simp only [tsum_mul_left] at hsum
  have heq : (∑' k, e k) = periodicL2Norm f ^ 2 :=
    hf.periodicL2Norm_sq_eq_tsum.symm
  have hmq : (∑' k, (1 + frequencyNorm k ^ 2) ^ (m : ℝ) * e k) =
      periodicSobolevNorm m f ^ 2 := by
    exact (Real.sq_sqrt (tsum_nonneg (fun k ↦ by dsimp [e]; positivity))).symm
  rw [heq, hmq] at hsum
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold periodicL2Norm periodicSobolevNorm; positivity, ?_⟩
  change (∑' k, (1 + frequencyNorm k ^ 2) ^ (r : ℝ) * e k) ≤ _
  have hn : 0 ≤ R ^ (r : ℝ) * periodicL2Norm f *
      (R ^ ((r : ℝ) - m) * periodicSobolevNorm m f) := by
    unfold periodicL2Norm periodicSobolevNorm
    positivity
  nlinarith

/-- The choice `m > max(r, 2A/(1-t))` preceding `main:eq:fine-source-profile`.
The order depends on the requested derivative order and fixed exponents only. -/
theorem exists_preparedResidual_high_order {t : ℝ} (ht : t < 1) (A : ℝ) (r : ℕ) :
    ∃ m : ℕ, r < m ∧ 2 * A < (1 - t) * m := by
  obtain ⟨m, hm, hgap⟩ := exists_nat_order_mul_gt (by linarith : 0 < 1 - t) (2 * A) (r + 1)
  exact ⟨m, hm, hgap⟩

/-- `main:eq:actual-fine-source`: a small L² norm and one sufficiently high
coarse profile give the sharp residual profile, with constant `1 + Cm`.
The analytic endpoint bounds are explicit inputs; the interpolation estimate
itself is proved by the Fourier split. -/
theorem preparedResidual_sobolev_profile {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {rc : Torus n → F} (hsm : IsSmoothPeriodic rc)
    {r m : ℕ} {R A t Cm : ℝ} (hR : 1 ≤ R) (hrm : r < m)
    (hgap : 2 * A < (1 - t) * m) (hCm : 0 ≤ Cm)
    (hzero : periodicL2Norm rc ≤ R ^ (-2 * A))
    (hhigh : periodicSobolevNorm m rc ≤ Cm * (R ^ t) ^ (m : ℝ)) :
    periodicSobolevNorm r rc ≤ (1 + Cm) * R ^ (-2 * A + r) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlow : R ^ (r : ℝ) * periodicL2Norm rc ≤ R ^ (-2 * A + r) := by
    calc
      _ ≤ R ^ (r : ℝ) * R ^ (-2 * A) :=
        mul_le_mul_of_nonneg_left hzero (Real.rpow_nonneg hRpos.le _)
      _ = _ := by rw [← Real.rpow_add hRpos]; congr 1; ring
  have hhi : R ^ ((r : ℝ) - m) * periodicSobolevNorm m rc ≤
      Cm * R ^ (-2 * A + r) := by
    calc
      _ ≤ R ^ ((r : ℝ) - m) * (Cm * (R ^ t) ^ (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhigh (Real.rpow_nonneg hRpos.le _)
      _ = Cm * R ^ ((r : ℝ) - m + t * m) := by
        rw [← Real.rpow_mul hRpos.le, mul_left_comm, ← Real.rpow_add hRpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hCm
  exact (periodicSobolevNorm_le_preparedSource_split hsm hrm.le hRpos).trans (by
    nlinarith)

/-- `main:eq:fine-source-profile`: the triangle estimate on the shared Sobolev
norm for the literal difference of smooth periodic fields. -/
theorem periodicSobolevNorm_sub_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f g : Torus n → F} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (r : ℕ) :
    periodicSobolevNorm r (f - g) ≤ periodicSobolevNorm r f + periodicSobolevNorm r g := by
  have hfLp : MemLp f 2 := hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hgLp : MemLp g 2 := hg.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hfg : IsSmoothPeriodic (f - g) := ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
  rw [← hf.gradeNorm_toLp r hfLp, ← hg.gradeNorm_toLp r hgLp,
    ← hfg.gradeNorm_toLp r (hfLp.sub hgLp), MemLp.toLp_sub]
  exact (periodicSobolevScale n F).gradeNorm_sub_le
    (hf.toLp_mem_periodicSobolevLevel r hfLp) (hg.toLp_mem_periodicSobolevLevel r hgLp)

end JanetCartan
