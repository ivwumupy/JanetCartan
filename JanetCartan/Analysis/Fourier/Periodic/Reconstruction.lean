module

public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction.Character
public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction.Summability
public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Fourier reconstruction and derivative majorants

Fourier inversion and termwise differentiation prove the derivative bound used in
`paper.tex`, `app:lem:sharp-fourier-embedding`, with the unit-torus physical frequencies
of `app:not:fourier`. The majorant is written explicitly, independently of interpolation.
The statements hold for real Banach codomains, hence in particular for finite-dimensional
real Hilbert spaces. Every series used below has an accompanying convergence proof.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Termwise Fourier reconstruction of derivatives from summable frequency moments
(`app:not:fourier`, `app:lem:sharp-fourier-embedding`). -/
theorem hasSum_iteratedFDeriv_periodicFourierMode {f : Torus n → F}
    (hf : Continuous f) {r : ℕ}
    (hs : ∀ j ≤ r, Summable (fun k ↦ frequencyNorm k ^ j *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖)))
    {j : ℕ} (hj : j ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun k ↦ iteratedFDeriv ℝ j
      (periodicLift (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
        (periodicFourierCoeff f k).2)) x) (iteratedFDeriv ℝ j (periodicLift f) x) := by
  have hs₀ : Summable (fun k ↦ ‖(periodicFourierCoeff f k).1‖ +
      ‖(periodicFourierCoeff f k).2‖) := by simpa using hs 0 (Nat.zero_le r)
  have heq : periodicLift f = fun y ↦ ∑' k, periodicLift
      (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
        (periodicFourierCoeff f k).2) y := by
    funext y
    exact (hasSum_periodicFourierMode hf hs₀ (torusQuotient y)).tsum_eq.symm
  have hd := iteratedFDeriv_tsum_apply (N := (r : ℕ∞))
    (f := fun k ↦ periodicLift (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
      (periodicFourierCoeff f k).2))
    (v := fun l k ↦ frequencyNorm k ^ l *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖))
    (fun k ↦ (contDiff_periodicLift_periodicFourierMode k _ _).of_le (by simp))
    (fun l hl ↦ hs l (by exact_mod_cast hl))
    (fun l k y _ ↦ norm_iteratedFDeriv_periodicFourierMode_le k _ _ l y)
    (by exact_mod_cast hj) x
  rw [← heq] at hd
  rw [hd]
  exact (Summable.of_norm_bounded (hs j hj)
    (fun k ↦ norm_iteratedFDeriv_periodicFourierMode_le k _ _ j x)).hasSum

/-- The finite-support derivative bound required by `BernsteinL2`, derived from
Fourier inversion (`app:not:fourier`, `app:lem:sharp-fourier-embedding`). -/
theorem norm_iteratedFDeriv_periodicLift_le_sum_of_support {f : Torus n → F}
    (hf : Continuous f) (s : Finset (Fin n → ℤ))
    (hs : ∀ k ∉ s, periodicFourierCoeff f k = 0) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
      ∑ k ∈ s, frequencyNorm k ^ j *
        (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) := by
  have hzero (l : ℕ) : ∀ k ∉ s, frequencyNorm k ^ l *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) = 0 := by
    intro k hk
    simp [hs k hk]
  exact (hasSum_iteratedFDeriv_periodicFourierMode hf
    (r := j) (fun l _ ↦ summable_of_ne_finset_zero (hzero l)) le_rfl x).norm_le_of_bounded
      (hasSum_sum_of_ne_finset_zero (hzero j))
      (fun k ↦ norm_iteratedFDeriv_periodicFourierMode_le k _ _ j x)

/-- Frequency support gives the pointwise Fourier bound used in the L² Bernstein
estimate, with no reconstruction premise (`app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.norm_iteratedFDeriv_le_sum_frequencyBall {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {L : ℝ} (hL : HasFourierSupport L f) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
      ∑ k ∈ frequencyBall n L, frequencyNorm k ^ j *
        (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) :=
  norm_iteratedFDeriv_periodicLift_le_sum_of_support hf.1 (frequencyBall n L)
    (fun k hk ↦ hL k (lt_of_not_ge (fun h ↦ hk (mem_frequencyBall.mpr h)))) j x

/-- Smooth finite-dimensional real Hilbert-valued fields have absolutely convergent
Fourier reconstructions at every derivative order. All frequency moments needed for
termwise differentiation follow from smoothness (`app:not:fourier`). -/
theorem IsSmoothPeriodic.hasSum_iteratedFDeriv_fourier_of_smooth {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    {f : Torus n → G} (hf : IsSmoothPeriodic f) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun k ↦ iteratedFDeriv ℝ j
      (periodicLift (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
        (periodicFourierCoeff f k).2)) x) (iteratedFDeriv ℝ j (periodicLift f) x) :=
  hasSum_iteratedFDeriv_periodicFourierMode hf.1
    (r := j) (fun l _ ↦ hf.summable_frequencyNorm_pow_coeff l) le_rfl x

omit [CompleteSpace F] [NormedSpace ℝ F] [NormedAddCommGroup F] in
/-- Every lower frequency power is controlled by the Bessel weight
(`app:lem:sharp-fourier-embedding`). -/
theorem frequencyNorm_pow_le_besselWeight (k : Fin n → ℤ) {j r : ℕ} (hj : j ≤ r) :
    frequencyNorm k ^ j ≤ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) := by
  have hpos : 0 ≤ 1 + frequencyNorm k ^ 2 := by positivity
  have hfreq : 0 ≤ frequencyNorm k := by unfold frequencyNorm; positivity
  have hbase : frequencyNorm k ≤ Real.sqrt (1 + frequencyNorm k ^ 2) := by
    have he := Real.sq_sqrt hpos
    have hn := Real.sqrt_nonneg (1 + frequencyNorm k ^ 2)
    nlinarith
  calc
    _ ≤ (Real.sqrt (1 + frequencyNorm k ^ 2)) ^ j := pow_le_pow_left₀ hfreq hbase j
    _ = (1 + frequencyNorm k ^ 2) ^ ((j : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (frequencyNorm k)])
      (by gcongr)

omit [CompleteSpace F] in
/-- Summability of the explicit Bessel majorant gives every lower frequency moment
needed for derivative reconstruction (`app:lem:sharp-fourier-embedding`). -/
theorem summable_frequencyNorm_pow_mul_coeff_norms {f : Torus n → F} {r : ℕ}
    (hs : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
      Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
        ‖(periodicFourierCoeff f k).2‖ ^ 2))) {j : ℕ} (hj : j ≤ r) :
    Summable (fun k ↦ frequencyNorm k ^ j *
      (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖)) := by
  apply Summable.of_nonneg_of_le (fun k ↦ by unfold frequencyNorm; positivity) _
    (hs.mul_left (Real.sqrt 2))
  intro k
  calc
    _ ≤ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
        (Real.sqrt 2 * Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
          ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
      apply mul_le_mul (frequencyNorm_pow_le_besselWeight k hj)
        (norm_add_norm_le_sqrt_two_mul _ _) (by positivity) (by positivity)
    _ = _ := by ring

/-- Derivative Fourier inversion under the manuscript's summable weighted coefficient
hypothesis (`app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.hasSum_iteratedFDeriv_fourier {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {r : ℕ}
    (hs : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
      Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
        ‖(periodicFourierCoeff f k).2‖ ^ 2)))
    {j : ℕ} (hj : j ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun k ↦ iteratedFDeriv ℝ j
      (periodicLift (periodicFourierModeOfParts k (periodicFourierCoeff f k).1
        (periodicFourierCoeff f k).2)) x) (iteratedFDeriv ℝ j (periodicLift f) x) :=
  hasSum_iteratedFDeriv_periodicFourierMode hf.1
    (fun _ hl ↦ summable_frequencyNorm_pow_mul_coeff_norms hs hl) hj x

/-- Every derivative up to order `r` is bounded by the explicit summable Fourier
majorant (`app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.norm_iteratedFDeriv_le_fourier_majorant {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {r : ℕ}
    (hs : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
      Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
        ‖(periodicFourierCoeff f k).2‖ ^ 2)))
    {j : ℕ} (hj : j ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤ Real.sqrt 2 *
      ∑' k, (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
        Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
          ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  apply (hf.hasSum_iteratedFDeriv_fourier hs hj x).norm_le_of_bounded
    (hs.hasSum.mul_left (Real.sqrt 2))
  intro k
  calc
    _ ≤ frequencyNorm k ^ j *
        (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) :=
      norm_iteratedFDeriv_periodicFourierMode_le k _ _ j x
    _ ≤ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
        (Real.sqrt 2 * Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
          ‖(periodicFourierCoeff f k).2‖ ^ 2)) :=
      mul_le_mul (frequencyNorm_pow_le_besselWeight k hj)
        (norm_add_norm_le_sqrt_two_mul _ _) (by positivity) (by positivity)
    _ = _ := by ring

/-- The sum-of-suprema Cʳ seminorm bound obtained from Fourier reconstruction
(`app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.cNorm_le_fourier_majorant {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {r : ℕ}
    (hs : Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
      Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
        ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      (((r : ℝ) + 1) * Real.sqrt 2) *
        ∑' k, (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
          Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
            ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  unfold cNorm
  calc
    _ ≤ ∑ _j ∈ Finset.range (r + 1), Real.sqrt 2 *
        ∑' k, (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
          Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 +
            ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      apply csSup_le ((fundamentalCell_nonempty n).image _)
      rintro _ ⟨x, _, rfl⟩
      exact hf.norm_iteratedFDeriv_le_fourier_majorant hs
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]; ring

end JanetCartan
