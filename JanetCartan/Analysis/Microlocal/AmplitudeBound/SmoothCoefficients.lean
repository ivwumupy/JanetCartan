module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.CoefficientDecay
public import JanetCartan.Analysis.Fourier.Periodic.Deriv

/-!
# Coefficient bounds from physical derivatives

The integration-by-parts step of `app:ch_osc:lem:osc-amplitude`, for complex
amplitudes on the auxiliary unit torus. Only the zeroth and the pure derivatives
of order `2(d+1)` enter the estimate. Periodizing a compactly supported Euclidean
amplitude on a larger torus remains a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.AmplitudeBound

variable {n : ℕ}

/-- The complex mixed derivative identity used for `app:ch_osc:lem:osc-amplitude`. -/
theorem mFourierCoeff_complex_coordinateDerivList {f : Torus n → ℂ}
    (hf : IsSmoothPeriodic f) (is : List (Fin n)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicCoordinateDerivList is f) k =
      (is.map (fun i ↦ 2 * Real.pi * Complex.I * (k i : ℂ))).prod *
        UnitAddTorus.mFourierCoeff f k := by
  induction is with
  | nil => simp [periodicCoordinateDerivList]
  | cons i is ih =>
    rw [periodicCoordinateDerivList, mFourierCoeff_coordinateDeriv
      (hf.coordinateDerivList is), ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- A pure complex derivative controls its Fourier coefficient
(`app:ch_osc:lem:osc-amplitude`). -/
theorem pow_mul_norm_complex_mFourierCoeff_le {f : Torus n → ℂ}
    (hf : IsSmoothPeriodic f) (i : Fin n) (r : ℕ) {A : ℝ}
    (hA : ∀ x, ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ A)
    (k : Fin n → ℤ) :
    (2 * Real.pi * |(k i : ℝ)|) ^ r * ‖UnitAddTorus.mFourierCoeff f k‖ ≤ A := by
  have h := norm_mFourierCoeff_le _ k hA
  rw [mFourierCoeff_complex_coordinateDerivList hf] at h
  simpa [norm_mul, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, Int.cast_abs] using h

/-- Radial coefficient control from pure derivatives, with the physical `2π`
frequency convention of `app:ch_osc:lem:osc-amplitude`. -/
theorem frequencyNorm_pow_mul_norm_complex_mFourierCoeff_le {f : Torus n → ℂ}
    (hf : IsSmoothPeriodic f) (hn : 0 < n) (r : ℕ) {A : ℝ}
    (hA : ∀ i x, ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ A)
    (k : Fin n → ℤ) :
    frequencyNorm k ^ r * ‖UnitAddTorus.mFourierCoeff f k‖ ≤ (n : ℝ) ^ r * A := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n ↦ |(k i : ℝ)|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have he : (WithLp.toLp 2 (fun j ↦ (k j : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      ∑ j, EuclideanSpace.single j (k j : ℝ) := by ext j; simp
  have hfreq : frequencyNorm k ≤ (n : ℝ) * (2 * Real.pi * |(k i : ℝ)|) := by
    unfold frequencyNorm
    rw [he]
    calc
      _ ≤ 2 * Real.pi * ∑ j : Fin n, ‖EuclideanSpace.single j (k j : ℝ)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ 2 * Real.pi * ∑ _j : Fin n, |(k i : ℝ)| := by
        gcongr with j
        simpa using hi j (Finset.mem_univ _)
      _ = _ := by simp; ring
  calc
    _ ≤ ((n : ℝ) * (2 * Real.pi * |(k i : ℝ)|)) ^ r *
        ‖UnitAddTorus.mFourierCoeff f k‖ := by
      gcongr
      exact mul_nonneg (by positivity) (norm_nonneg _)
    _ = (n : ℝ) ^ r * ((2 * Real.pi * |(k i : ℝ)|) ^ r *
        ‖UnitAddTorus.mFourierCoeff f k‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_norm_complex_mFourierCoeff_le
      hf i r (hA i) k) (by positivity)

/-- An explicit constant for the physical coefficient decay in
`app:ch_osc:lem:osc-amplitude`, on the unit torus. -/
def smoothCoefficientConstant (d : ℕ) : ℝ :=
  2 ^ d * (1 + (2 * d : ℝ) ^ (2 * (d + 1)))

/-- Positivity of the coefficient constant in `app:ch_osc:lem:osc-amplitude`. -/
theorem smoothCoefficientConstant_pos (d : ℕ) : 0 < smoothCoefficientConstant d := by
  unfold smoothCoefficientConstant
  positivity

/-- The exact summable decay of `app:ch_osc:lem:osc-amplitude` follows from the
stated number of physical derivatives. This is uniform in any external parameter. -/
theorem norm_mFourierCoeff_le_twoPositionWeight {d : ℕ} (hd : 0 < d)
    {f : Torus (2 * d) → ℂ} (hf : IsSmoothPeriodic f) {A : ℝ}
    (hzero : ∀ x, ‖f x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) f x‖ ≤ A)
    (k : Fin (2 * d) → ℤ) :
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤
      (smoothCoefficientConstant d * A) * twoPositionWeight d k := by
  have hz := norm_mFourierCoeff_le f k hzero
  have hr := frequencyNorm_pow_mul_norm_complex_mFourierCoeff_le hf (by omega)
    (2 * (d + 1)) hderiv k
  have hp : 0 < (1 + frequencyNorm k ^ 2) ^ (d + 1) := by positivity
  have hpoly : (1 + frequencyNorm k ^ 2) ^ (d + 1) *
      ‖UnitAddTorus.mFourierCoeff f k‖ ≤ smoothCoefficientConstant d * A := by
    calc
      _ ≤ (2 ^ d * (1 + frequencyNorm k ^ (2 * (d + 1)))) *
          ‖UnitAddTorus.mFourierCoeff f k‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa [pow_mul] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
          (sq_nonneg (frequencyNorm k)) (d + 1)
      _ = 2 ^ d * (‖UnitAddTorus.mFourierCoeff f k‖ +
          frequencyNorm k ^ (2 * (d + 1)) * ‖UnitAddTorus.mFourierCoeff f k‖) := by ring
      _ ≤ 2 ^ d * (A + (2 * d : ℝ) ^ (2 * (d + 1)) * A) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hz _) (by positivity)
        exact_mod_cast hr
      _ = _ := by unfold smoothCoefficientConstant; ring
  have hw : twoPositionWeight d k = ((1 + frequencyNorm k ^ 2) ^ (d + 1))⁻¹ := by
    unfold twoPositionWeight
    rw [show -((d : ℝ) + 1) = -((d + 1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hw, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hpoly)

/-- Absolute summability of the actual physical Fourier coefficients in
`app:ch_osc:lem:osc-amplitude`. -/
theorem summable_norm_mFourierCoeff_of_twoPosition_derivatives {d : ℕ} (hd : 0 < d)
    {f : Torus (2 * d) → ℂ} (hf : IsSmoothPeriodic f) {A : ℝ}
    (hzero : ∀ x, ‖f x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) f x‖ ≤ A) :
    Summable (fun k ↦ ‖UnitAddTorus.mFourierCoeff f k‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_mFourierCoeff_le_twoPositionWeight hd hf hzero hderiv)
    ((summable_twoPositionWeight d).mul_left _)

/-- The absolutely summable physical Fourier expansion reconstructs the smooth
amplitude everywhere, as required in `app:ch_osc:lem:osc-amplitude`. -/
theorem hasSum_mFourierCoeff_of_twoPosition_derivatives {d : ℕ} (hd : 0 < d)
    {f : Torus (2 * d) → ℂ} (hf : IsSmoothPeriodic f) {A : ℝ}
    (hzero : ∀ x, ‖f x‖ ≤ A)
    (hderiv : ∀ i x,
      ‖periodicCoordinateDerivList (List.replicate (2 * (d + 1)) i) f x‖ ≤ A)
    (x : Torus (2 * d)) :
    HasSum (fun k ↦ UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x) (f x) :=
  UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := ⟨f, hf.1⟩)
    (summable_norm_mFourierCoeff_of_twoPosition_derivatives hd hf hzero hderiv).of_norm x

end JanetCartan.AmplitudeBound
