module

public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Spectral part of the cutoff estimates

The estimates in `main:lem:smoothing` use the physical-frequency convention of
`Periodic`. These lemmas bound the Sobolev size of a field with exact Fourier support.
The unweighted Fourier energy is assumed summable; the weighted summability is proved.
No Parseval identity or cutoff construction is assumed implicitly.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem fourierEnergy_weight_le_of_support {L : ℝ} {f : Torus n → F}
    (hf : HasFourierSupport L f) (r : ℕ) (k : Fin n → ℤ) :
    (1 + frequencyNorm k ^ 2) ^ r *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) ≤
      (1 + L ^ 2) ^ r *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  by_cases hk : frequencyNorm k ≤ L
  · have hfreq : 0 ≤ frequencyNorm k := by unfold frequencyNorm; positivity
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by nlinarith) r) (by positivity)
  · have hz := hf k (lt_of_not_ge hk)
    simp [hz]

/-- `main:lem:smoothing`: finite Fourier support upgrades summable Fourier energy
    to summability at every nonnegative integer Sobolev order. -/
theorem summable_sobolevEnergy_of_hasFourierSupport {L : ℝ} {f : Torus n → F}
    (hf : HasFourierSupport L f)
    (hs : Summable (fun k : Fin n → ℤ ↦
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
    (r : ℕ) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (r : ℝ) *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
  simp only [Real.rpow_natCast]
  exact Summable.of_nonneg_of_le (fun _ ↦ by positivity)
    (fourierEnergy_weight_le_of_support hf r) (hs.mul_left ((1 + L ^ 2) ^ r))

/-- `main:eq:smoothing-low`: the spectral Sobolev bound at integer order.
    The order-zero Fourier norm can subsequently be identified with L² by Parseval. -/
theorem periodicSobolevNorm_le_of_hasFourierSupport {L : ℝ} {f : Torus n → F}
    (hf : HasFourierSupport L f)
    (hs : Summable (fun k : Fin n → ℤ ↦
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
    (r : ℕ) :
    periodicSobolevNorm (r : ℝ) f ≤
      Real.sqrt ((1 + L ^ 2) ^ r) * periodicSobolevNorm 0 f := by
  have hsum := summable_sobolevEnergy_of_hasFourierSupport hf hs r
  simp only [Real.rpow_natCast] at hsum
  have hle := hsum.tsum_le_tsum (fourierEnergy_weight_le_of_support hf r)
    (hs.mul_left ((1 + L ^ 2) ^ r))
  simp only [periodicSobolevNorm, Real.rpow_natCast, Real.rpow_zero, one_mul]
  apply le_trans (Real.sqrt_le_sqrt hle)
  rw [tsum_mul_left, Real.sqrt_mul (by positivity)]

/-- `main:eq:smoothing-low`: support below `2 * R`, with `R ≥ 1`, gives the
    required `R ^ r` Sobolev scaling, with the explicit constant `(√5) ^ r`. -/
theorem periodicSobolevNorm_le_scale_of_hasFourierSupport {R : ℝ} (hR : 1 ≤ R)
    {f : Torus n → F} (hf : HasFourierSupport (2 * R) f)
    (hs : Summable (fun k : Fin n → ℤ ↦
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
    (r : ℕ) :
    periodicSobolevNorm (r : ℝ) f ≤
      Real.sqrt 5 ^ r * R ^ r * periodicSobolevNorm 0 f := by
  apply (periodicSobolevNorm_le_of_hasFourierSupport hf hs r).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · calc
      (1 + (2 * R) ^ 2) ^ r ≤ (5 * R ^ 2) ^ r :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) r
      _ = (Real.sqrt 5 ^ r * R ^ r) ^ 2 := by
        rw [← mul_pow, ← pow_mul, mul_comm r 2, pow_mul]
        congr 1
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private theorem sobolevEnergy_le_of_real_multiplier {f g : Torus n → F}
    (m : (Fin n → ℤ) → ℝ)
    (hcoeff : ∀ k, periodicFourierCoeff g k = m k • periodicFourierCoeff f k)
    {M : ℝ} (hm : ∀ k, |m k| ≤ M) (s : ℝ) (k : Fin n → ℤ) :
    (1 + frequencyNorm k ^ 2) ^ s *
        (‖(periodicFourierCoeff g k).1‖ ^ 2 + ‖(periodicFourierCoeff g k).2‖ ^ 2) ≤
      M ^ 2 * ((1 + frequencyNorm k ^ 2) ^ s *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
  rw [hcoeff k]
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs, mul_pow]
  have hsq : |m k| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hm k) 2
  have henergy : 0 ≤ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2 := by positivity
  have hw : 0 ≤ (1 + frequencyNorm k ^ 2) ^ s := Real.rpow_nonneg (by positivity) _
  nlinarith [mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hsq henergy) hw]

/-- `main:lem:smoothing`: a bounded real Fourier multiplier preserves summability
    of the Sobolev energy. The coefficient identity is an explicit input. -/
theorem summable_sobolevEnergy_of_real_multiplier {f g : Torus n → F}
    (m : (Fin n → ℤ) → ℝ)
    (hcoeff : ∀ k, periodicFourierCoeff g k = m k • periodicFourierCoeff f k)
    {M : ℝ} (hm : ∀ k, |m k| ≤ M) (s : ℝ)
    (hs : Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff g k).1‖ ^ 2 + ‖(periodicFourierCoeff g k).2‖ ^ 2)) := by
  exact Summable.of_nonneg_of_le (fun _ ↦ by positivity)
    (sobolevEnergy_le_of_real_multiplier m hcoeff hm s) (hs.mul_left (M ^ 2))

/-- `main:eq:smoothing-low`: a real Fourier multiplier bounded by `M` has
    Sobolev norm at most `M` times that of its input, at every real order with
    summable input energy. In particular, a symbol in `[0, 1]` is contractive. -/
theorem periodicSobolevNorm_le_of_real_multiplier {f g : Torus n → F}
    (m : (Fin n → ℤ) → ℝ)
    (hcoeff : ∀ k, periodicFourierCoeff g k = m k • periodicFourierCoeff f k)
    {M : ℝ} (hM : 0 ≤ M) (hm : ∀ k, |m k| ≤ M) (s : ℝ)
    (hs : Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    periodicSobolevNorm s g ≤ M * periodicSobolevNorm s f := by
  have hg := summable_sobolevEnergy_of_real_multiplier m hcoeff hm s hs
  have hle := hg.tsum_le_tsum (sobolevEnergy_le_of_real_multiplier m hcoeff hm s)
    (hs.mul_left (M ^ 2))
  unfold periodicSobolevNorm
  apply le_trans (Real.sqrt_le_sqrt hle)
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]

omit [NormedSpace ℝ F] in
/-- `main:eq:smoothing-low`: normalized Haar measure bounds periodic L² size
    by any pointwise bound. The measure is the unit-torus measure of `Periodic`. -/
theorem periodicL2Norm_le_of_bound (f : Torus n → F) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x, ‖f x‖ ≤ M) : periodicL2Norm f ≤ M := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  apply Real.sqrt_le_iff.mpr
  refine ⟨hM, ?_⟩
  calc
    (∫ x, ‖f x‖ ^ 2) ≤ ∫ _ : Torus n, M ^ 2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
        (integrable_const _) (Filter.Eventually.of_forall (fun x ↦
          pow_le_pow_left₀ (norm_nonneg _) (hf x) 2))
    _ = _ := by simp

/-- `main:eq:smoothing-low`: the Sobolev estimate for a bounded real multiplier
    with support below `2 * R`, conditional on the exact Parseval `HasSum` identity.
    Both the multiplier identity and support must refer to the same output `g`. -/
theorem periodicSobolevNorm_le_scale_of_real_multiplier
    {f g : Torus n → F} (m : (Fin n → ℤ) → ℝ)
    (hcoeff : ∀ k, periodicFourierCoeff g k = m k • periodicFourierCoeff f k)
    {M A R : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hm : ∀ k, |m k| ≤ M) (hf : ∀ x, ‖f x‖ ≤ A)
    (hg : HasFourierSupport (2 * R) g)
    (hparseval : HasSum (fun k : Fin n → ℤ ↦
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)
      (∫ x, ‖f x‖ ^ 2)) (r : ℕ) :
    periodicSobolevNorm (r : ℝ) g ≤ Real.sqrt 5 ^ r * R ^ r * (M * A) := by
  have hs0 : Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (0 : ℝ) *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
    simpa only [Real.rpow_zero, one_mul] using hparseval.summable
  have hg0 := summable_sobolevEnergy_of_real_multiplier m hcoeff hm 0 hs0
  simp only [Real.rpow_zero, one_mul] at hg0
  have hzero : periodicSobolevNorm 0 f = periodicL2Norm f := by
    simp only [periodicSobolevNorm, periodicL2Norm, Real.rpow_zero, one_mul,
      hparseval.tsum_eq]
  have hbase : periodicSobolevNorm 0 g ≤ M * A := by
    calc
      _ ≤ M * periodicSobolevNorm 0 f :=
        periodicSobolevNorm_le_of_real_multiplier m hcoeff hM hm 0 hs0
      _ ≤ M * A := by
        rw [hzero]
        exact mul_le_mul_of_nonneg_left (periodicL2Norm_le_of_bound f hA hf) hM
  exact (periodicSobolevNorm_le_scale_of_hasFourierSupport hR hg hg0 r).trans
    (mul_le_mul_of_nonneg_left hbase (by positivity))

end JanetCartan
