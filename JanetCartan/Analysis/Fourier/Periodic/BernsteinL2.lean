module

public import JanetCartan.Analysis.Fourier.Periodic.BernsteinL2.Modes
public import JanetCartan.Analysis.Fourier.Periodic.BernsteinL2.Reconstruction
public import JanetCartan.Analysis.Fourier.Periodic.Parseval

/-!
# Band-limited L² to C^r Bernstein estimates

The sharp exponent `r + n / 2` in `main:eq:history-bernstein` and
`main:eq:final-Cr` of paper.tex, with the unit-torus `2π` convention.
Finite Fourier reconstruction and the mode derivative estimate reduce the proof
to Cauchy–Schwarz, Parseval, and the physical-frequency lattice count.

The unconditional result `cNorm_periodicLift_le_of_hasFourierSupport` applies to
smooth fields in finite-dimensional real inner product spaces, including Euclidean
vectors and matrices with their Frobenius norm. Its constant is independent of the
bandwidth and the field. Continuity already suffices, as recorded separately.
-/

@[expose] public noncomputable section

open scoped BigOperators ContDiff

namespace JanetCartan
namespace BernsteinL2

/-- `main:eq:final-Cr`: finite Cauchy–Schwarz for the two real components of
Fourier coefficients. The bound includes both components in the energy. -/
theorem sum_add_le_sqrt_card_mul {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∑ k ∈ s, (a k ^ 2 + b k ^ 2) ≤ B ^ 2) :
    ∑ k ∈ s, (a k + b k) ≤ Real.sqrt (2 * (s.card : ℝ)) * B := by
  have hcs : (∑ k ∈ s, (a k + b k)) ^ 2 ≤
      (s.card : ℝ) * ∑ k ∈ s, (a k + b k) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ)) (fun k ↦ a k + b k)
  have hp : ∑ k ∈ s, (a k + b k) ^ 2 ≤ 2 * ∑ k ∈ s, (a k ^ 2 + b k ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ ↦ by nlinarith [sq_nonneg (a k - b k)])
  have hsq : (∑ k ∈ s, (a k + b k)) ^ 2 ≤ 2 * (s.card : ℝ) * B ^ 2 := by
    calc
      _ ≤ (s.card : ℝ) * ∑ k ∈ s, (a k + b k) ^ 2 := hcs
      _ ≤ (s.card : ℝ) * (2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hp.trans (mul_le_mul_of_nonneg_left henergy (by norm_num))) (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt (2 * (s.card : ℝ) * B ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB]

/-- `main:eq:history-bernstein`: pass uniform geometric derivative bounds to the
sum of derivative suprema defining `cNorm`. -/
theorem cNorm_le_of_iteratedFDeriv_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : s.Nonempty) (r : ℕ) (f : E → F) {L B : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ r, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ L ^ j * B) :
    cNorm s r f ≤ (r + 1 : ℝ) * L ^ r * B := by
  calc
    cNorm s r f ≤ ∑ _j ∈ Finset.range (r + 1), L ^ r * B := by
      apply Finset.sum_le_sum
      intro j hj
      apply csSup_le (hs.image _)
      rintro _ ⟨x, hx, rfl⟩
      exact (hderiv j (by simpa using hj) x hx).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by simpa using hj)) hB)
    _ = _ := by simp [Nat.cast_add, Nat.cast_one, mul_assoc]

/-- `main:eq:final-Cr`: an `O(L^n)` frequency count contributes precisely
`L^(n/2)` to the Fourier Cauchy–Schwarz estimate. -/
theorem sqrt_two_card_le_of_card_le {ι : Type*} (s : Finset ι) (n : ℕ) {C L : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C) (hcard : (s.card : ℝ) ≤ C * L ^ n) :
    Real.sqrt (2 * (s.card : ℝ)) ≤ Real.sqrt (2 * C) * L ^ ((n : ℝ) / 2) := by
  calc
    _ ≤ Real.sqrt (2 * (C * L ^ n)) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt (2 * C) * Real.sqrt (L ^ n) := by
      rw [← mul_assoc, Real.sqrt_mul (by positivity)]
    _ = _ := by
      rw [Real.sqrt_eq_rpow (L ^ n), ← Real.rpow_natCast_mul hL.le]
      congr 2
      ring

end BernsteinL2

section Normed

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:history-bernstein`: a finite Parseval bound controls the sum of
the norms of the real and imaginary Fourier coefficients. -/
theorem sum_norm_periodicFourierCoeff_le (f : Torus n → F) (s : Finset (Fin n → ℤ))
    (henergy : ∑ k ∈ s,
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) ≤
        periodicL2Norm f ^ 2) :
    ∑ k ∈ s, (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) ≤
      Real.sqrt (2 * (s.card : ℝ)) * periodicL2Norm f :=
  BernsteinL2.sum_add_le_sqrt_card_mul s
    (fun k ↦ ‖(periodicFourierCoeff f k).1‖) (fun k ↦ ‖(periodicFourierCoeff f k).2‖)
    (Real.sqrt_nonneg _) henergy

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: the sharp L² to C^r estimate
conditional on the frequency count, finite Parseval bound, and pointwise Fourier
derivative estimate. The analytic inputs of this
reduction are discharged in `cNorm_periodicLift_le_of_hasFourierSupport` below. -/
theorem cNorm_periodicLift_le_of_fourier_bounds (r : ℕ) (f : Torus n → F)
    (s : Finset (Fin n → ℤ)) {C L : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hfrequency : ∀ k ∈ s, frequencyNorm k ≤ L)
    (hcard : (s.card : ℝ) ≤ C * L ^ n)
    (henergy : ∑ k ∈ s,
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) ≤
        periodicL2Norm f ^ 2)
    (hderiv : ∀ j ≤ r, ∀ x ∈ fundamentalCell n,
      ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
        ∑ k ∈ s, frequencyNorm k ^ j *
          (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖)) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      ((r + 1 : ℝ) * Real.sqrt (2 * C)) * L ^ ((r : ℝ) + (n : ℝ) / 2) *
        periodicL2Norm f := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hnorm : 0 ≤ periodicL2Norm f := Real.sqrt_nonneg _
  have hsum := sum_norm_periodicFourierCoeff_le f s henergy
  have hcount := BernsteinL2.sqrt_two_card_le_of_card_le s n hLpos hC hcard
  have hcell : (fundamentalCell n).Nonempty := ⟨0, fun i ↦ by simp⟩
  have hpoint : ∀ j ≤ r, ∀ x ∈ fundamentalCell n,
      ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
        L ^ j * (Real.sqrt (2 * (s.card : ℝ)) * periodicL2Norm f) := by
    intro j hj x hx
    calc
      _ ≤ ∑ k ∈ s, frequencyNorm k ^ j *
          (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) :=
        hderiv j hj x hx
      _ ≤ ∑ k ∈ s, L ^ j *
          (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by unfold frequencyNorm; positivity) (hfrequency k hk) j
      _ = L ^ j * ∑ k ∈ s,
          (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (pow_nonneg hLpos.le j)
  calc
    _ ≤ (r + 1 : ℝ) * L ^ r *
        (Real.sqrt (2 * (s.card : ℝ)) * periodicL2Norm f) :=
      BernsteinL2.cNorm_le_of_iteratedFDeriv_le hcell r (periodicLift f) hL
        (mul_nonneg (Real.sqrt_nonneg _) hnorm) hpoint
    _ ≤ (r + 1 : ℝ) * L ^ r *
        ((Real.sqrt (2 * C) * L ^ ((n : ℝ) / 2)) * periodicL2Norm f) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcount hnorm
    _ = _ := by
      rw [Real.rpow_add hLpos, Real.rpow_natCast]
      ring

end Normed

variable {n : ℕ}

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: pointwise derivatives of a
band-limited field are bounded by the finite frequency-weighted coefficient sum. -/
theorem norm_iteratedFDeriv_periodicLift_le_sum {f : Torus n → F} (hf : Continuous f)
    {L : ℝ} (hs : HasFourierSupport L f) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (periodicLift f) x‖ ≤
      ∑ k ∈ frequencyBall n L, frequencyNorm k ^ j *
        (‖(periodicFourierCoeff f k).1‖ + ‖(periodicFourierCoeff f k).2‖) := by
  have heq : periodicLift f = fun y ↦ ∑ k ∈ frequencyBall n L,
      periodicLift (periodicFourierMode k (periodicFourierCoeff f k)) y := by
    funext y
    exact eq_sum_periodicFourierMode_of_hasFourierSupport hf hs (torusQuotient y)
  rw [heq, iteratedFDeriv_sum (fun k _ ↦
    (isSmoothPeriodic_periodicFourierMode k (periodicFourierCoeff f k)).2.of_le (by simp))]
  simp only [Finset.sum_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦
    BernsteinL2.norm_iteratedFDeriv_periodicFourierMode_le k _ j x)

end Banach

section Hilbert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `app:not:fourier`, `main:eq:final-Cr`: finite Fourier energy is bounded by
the squared normalized L² norm, as a consequence of convergent Parseval. -/
theorem sum_sq_periodicFourierCoeff_le {f : Torus n → F} (hf : Continuous f)
    (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, (‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) ≤ periodicL2Norm f ^ 2 := by
  have h := hasSum_sq_periodicFourierCoeff_of_continuous hf
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum s (fun _ _ ↦ by positivity)

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: sharp Bernstein estimate
for continuous band-limited fields, with an explicit constant uniform in `L` and `f`. -/
theorem cNorm_periodicLift_le_of_continuous_hasFourierSupport {f : Torus n → F} (hf : Continuous f)
    {L : ℝ} (hL : 1 ≤ L) (hs : HasFourierSupport L f) (r : ℕ) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      ((r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)) * L ^ ((r : ℝ) + (n : ℝ) / 2) *
        periodicL2Norm f := by
  apply cNorm_periodicLift_le_of_fourier_bounds r f (frequencyBall n L) hL (by positivity)
  · exact fun _ hk ↦ mem_frequencyBall.mp hk
  · exact card_frequencyBall_le hL
  · exact sum_sq_periodicFourierCoeff_le hf _
  · exact fun j _ x _ ↦ norm_iteratedFDeriv_periodicLift_le_sum hf hs j x

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: smooth band-limited fields
satisfy the L² to C^r bound with exact exponent `r + n / 2`, without derivative loss. -/
theorem cNorm_periodicLift_le_of_hasFourierSupport {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {L : ℝ} (hL : 1 ≤ L) (hs : HasFourierSupport L f) (r : ℕ) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      ((r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)) * L ^ ((r : ℝ) + (n : ℝ) / 2) *
        periodicL2Norm f :=
  cNorm_periodicLift_le_of_continuous_hasFourierSupport hf.1 hL hs r

end Hilbert

end JanetCartan
