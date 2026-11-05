module

public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction.Series
public import JanetCartan.Analysis.Fourier.Periodic.Lattice

/-!
# Absolute summability of smooth Fourier series

Polynomial coefficient decay and convergent lattice power sums give every
frequency moment for smooth finite-dimensional real Hilbert-valued fields
(`paper.tex`, `app:not:fourier`, `app:lem:sharp-fourier-embedding`).
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan

variable {n : ℕ}

private theorem summable_frequencyNorm_pow_mul_complex_coeff {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (j : ℕ) :
    Summable (fun k ↦ frequencyNorm k ^ j *
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖) := by
  obtain ⟨C, hC, hdecay⟩ := hf.exists_mFourierCoeff_decay (j + (n + 1))
  have hsum := (summable_frequencyNorm_rpow (n := n)
    (p := (n + 1 : ℕ)) (by push_cast; linarith)).mul_left C
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [Filter.eventually_cofinite_ne 0] with k hk
  have hp := frequencyNorm_pos_of_ne_zero k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hp.le j) (norm_nonneg _))]
  calc
    _ ≤ frequencyNorm k ^ j * (C / frequencyNorm k ^ (j + (n + 1))) :=
      mul_le_mul_of_nonneg_left (hdecay k hk) (pow_nonneg hp.le j)
    _ = C * frequencyNorm k ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hp.le, Real.rpow_natCast, pow_add]
      field_simp

/-- Scalar smooth Fourier coefficients have every absolutely summable frequency
moment (`app:not:fourier`). -/
theorem IsSmoothPeriodic.summable_frequencyNorm_pow_coeff_real {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (j : ℕ) :
    Summable (fun k ↦ frequencyNorm k ^ j *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖)) := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg
    (pow_nonneg (frequencyNorm_nonneg k) j) (by positivity)) _
    ((summable_frequencyNorm_pow_mul_complex_coeff hf j).mul_right 2)
  intro k
  rw [periodicFourierCoeff_eq_complex_parts hf.1]
  have hr := Complex.abs_re_le_norm (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k)
  have hi := Complex.abs_im_le_norm (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k)
  simp only [Real.norm_eq_abs]
  calc
    _ ≤ frequencyNorm k ^ j *
        (2 * ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (frequencyNorm_nonneg k) j)
    _ = _ := by ring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem norm_le_sum_norm_inner (b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    (v : F) : ‖v‖ ≤ ∑ i, ‖⟪b i, v⟫‖ := by
  calc
    _ = ‖∑ i, ⟪b i, v⟫ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, v⟫ • b i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, b.orthonormal.norm_eq_one]

/-- Every frequency moment of the real coefficient-pair norms is summable for a
smooth finite-dimensional Hilbert-valued field (`app:not:fourier`). -/
theorem IsSmoothPeriodic.summable_frequencyNorm_pow_coeff {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (j : ℕ) :
    Summable (fun k ↦ frequencyNorm k ^ j *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖)) := by
  let b := stdOrthonormalBasis ℝ F
  have hc (i : Fin (Module.finrank ℝ F)) :=
    (hf.comp_clm (innerSL ℝ (b i))).summable_frequencyNorm_pow_coeff_real j
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg
    (pow_nonneg (frequencyNorm_nonneg k) j) (by positivity)) _
    (summable_sum (s := Finset.univ) (fun i _ ↦ hc i))
  intro k
  simp_rw [periodicFourierCoeff_map (innerSL ℝ (b _)) hf.1]
  simp only [innerSL_apply_apply]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (norm_le_sum_norm_inner b _) (norm_le_sum_norm_inner b _))
      (pow_nonneg (frequencyNorm_nonneg k) j)

end JanetCartan
