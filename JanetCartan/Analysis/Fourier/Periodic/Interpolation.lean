module

public import JanetCartan.Analysis.Fourier.Periodic
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation.Summation
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation.Weights
public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import JanetCartan.Analysis.Fourier.Periodic.Reconstruction
public import JanetCartan.Analysis.Fourier.Periodic.Sobolev.DerivativeEnergy

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fourier interpolation at a prescribed scale

The unit-torus case of `app:lem:sharp-fourier-embedding`, including the
graded-profile corollary. Lattice counting and tail bounds give the spectral
estimate, Parseval identifies its order-zero norm with L², and derivative
Fourier reconstruction controls Cʳ. The final smooth-field estimates have
no additional reconstruction or summability premises.

The shared conventions use physical frequencies `2 * π * k` and the
Bessel-potential Sobolev norm. Derivative Parseval proves convergence of
the Sobolev energy; the frequency split then proves absolute summability
of the Fourier majorant.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The nonnegative Fourier summand controlling derivatives through order `r`
in `app:lem:sharp-fourier-embedding`. -/
def fourierInterpolationTerm (r : ℕ) (f : Torus n → F) (k : Fin n → ℤ) : ℝ :=
  (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) / 2) *
    Real.sqrt (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)

/-- The frequency split in `app:lem:sharp-fourier-embedding`, specialized to
the shared Sobolev norm. This proves summability and the spectral estimate
from explicit lattice estimates. It does not assume Fourier inversion. -/
theorem fourierInterpolation_sum_le_of_lattice_bounds
    (f : Torus n → F) {r m : ℕ} {K L H : ℝ} (hK : 1 ≤ K)
    (hL : 0 ≤ L) (hH : 0 ≤ H)
    (henergy : Summable (fun k : Fin n → ℤ ↦
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))
    (hweighted : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)))
    (hlow : Summable (fun k : Fin n → ℤ ↦
      if frequencyNorm k ≤ K then (1 + frequencyNorm k ^ 2) ^ (r : ℝ) else 0))
    (hhigh : Summable (fun k : Fin n → ℤ ↦
      if frequencyNorm k ≤ K then 0 else (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) - m)))
    (hlow_bound : (∑' k : Fin n → ℤ,
      if frequencyNorm k ≤ K then (1 + frequencyNorm k ^ 2) ^ (r : ℝ) else 0) ≤
        (L * K ^ ((r : ℝ) + (n : ℝ) / 2)) ^ 2)
    (hhigh_bound : (∑' k : Fin n → ℤ,
      if frequencyNorm k ≤ K then 0 else (1 + frequencyNorm k ^ 2) ^ ((r : ℝ) - m)) ≤
        (H * K ^ ((r : ℝ) + (n : ℝ) / 2 - m)) ^ 2) :
    Summable (fourierInterpolationTerm r f) ∧
      (∑' k, fourierInterpolationTerm r f k) ≤
        L * K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicSobolevNorm 0 f +
        H * K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨hsum, hsplit⟩ := summable_weighted_sqrt_and_le_split
    (fun k : Fin n → ℤ ↦ frequencyNorm k ≤ K)
    (ρ := fun k ↦ 1 + frequencyNorm k ^ 2)
    (e := fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2)
    (r := (r : ℝ)) (m := (m : ℝ))
    (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    hlow hhigh henergy hweighted
  refine ⟨hsum, hsplit.trans ?_⟩
  have hlo := (Real.sqrt_le_iff).2
    ⟨mul_nonneg hL (Real.rpow_nonneg hKpos.le _), hlow_bound⟩
  have hhi := (Real.sqrt_le_iff).2
    ⟨mul_nonneg hH (Real.rpow_nonneg hKpos.le _), hhigh_bound⟩
  simpa only [periodicSobolevNorm, Real.rpow_zero, one_mul] using
    add_le_add (mul_le_mul_of_nonneg_right hlo (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right hhi (Real.sqrt_nonneg _))

/-- Assembly of the Fourier inversion and spectral estimates from
`app:lem:sharp-fourier-embedding`. The inversion bound and Parseval are
explicit analytic inputs; this is not the unconditional embedding theorem. -/
theorem cNorm_le_fourierInterpolation_of_spectral_bound
    (f : Torus n → F) {r m : ℕ} {K D L H : ℝ}
    (hD : 0 ≤ D) (hK : 1 ≤ K)
    (hinversion : Summable (fourierInterpolationTerm r f) →
      cNorm (fundamentalCell n) r (periodicLift f) ≤
        D * ∑' k, fourierInterpolationTerm r f k)
    (hspectral : Summable (fourierInterpolationTerm r f) ∧
      (∑' k, fourierInterpolationTerm r f k) ≤
      L * K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicSobolevNorm 0 f +
      H * K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f)
    (hparseval : periodicSobolevNorm 0 f = periodicL2Norm f) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      (D * max L H) * (K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm f +
        K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f) := by
  have hKnonneg : 0 ≤ K := le_trans zero_le_one hK
  have hfirst : 0 ≤ K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm f :=
    mul_nonneg (Real.rpow_nonneg hKnonneg _) (Real.sqrt_nonneg _)
  have hsecond : 0 ≤ K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f :=
    mul_nonneg (Real.rpow_nonneg hKnonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ D * (L * K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicSobolevNorm 0 f +
        H * K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f) :=
      (hinversion hspectral.1).trans (mul_le_mul_of_nonneg_left hspectral.2 hD)
    _ ≤ _ := by
      rw [hparseval, mul_assoc L, mul_assoc H, mul_assoc D, mul_add (max L H)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (le_max_left L H) hfirst)
          (mul_le_mul_of_nonneg_right (le_max_right L H) hsecond)) hD

/-- Scale algebra for the graded-profile conclusion of
`app:lem:sharp-fourier-embedding`. Only the two endpoint bounds are used. -/
theorem twoTerm_bound_of_graded_endpoints {X E₀ Eₘ C C₀ Cₘ A K a m : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C)
    (hestimate : X ≤ C * (K ^ a * E₀ + K ^ (a - m) * Eₘ))
    (hzero : E₀ ≤ C₀ * A) (hhigh : Eₘ ≤ Cₘ * A * K ^ m) :
    X ≤ (C * (C₀ + Cₘ)) * A * K ^ a := by
  calc
    X ≤ C * (K ^ a * (C₀ * A) + K ^ (a - m) * (Cₘ * A * K ^ m)) :=
      hestimate.trans (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hzero (Real.rpow_nonneg hK.le _))
          (mul_le_mul_of_nonneg_left hhigh (Real.rpow_nonneg hK.le _))) hC)
    _ = _ := by
      have hpow : K ^ (a - m) * K ^ m = K ^ a := by
        rw [← Real.rpow_add hK, sub_add_cancel]
      calc
        _ = C * (C₀ * A * K ^ a + Cₘ * A * (K ^ (a - m) * K ^ m)) := by ring
        _ = _ := by rw [hpow]; ring

/-- The graded Sobolev profile corollary of `app:lem:sharp-fourier-embedding`,
conditional on the two-term estimate and the order-zero Parseval identity.
Only orders zero and `m` of the Sobolev profile are required. -/
theorem cNorm_le_gradedSobolevProfile_of_interpolation
    (f : Torus n → F) {r m : ℕ} {K C C₀ Cₘ A : ℝ}
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hinterpolation : cNorm (fundamentalCell n) r (periodicLift f) ≤
      C * (K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm f +
        K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f))
    (hparseval : periodicSobolevNorm 0 f = periodicL2Norm f)
    (hzero : periodicSobolevNorm 0 f ≤ C₀ * A)
    (hhigh : periodicSobolevNorm m f ≤ Cₘ * A * K ^ (m : ℝ)) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      (C * (C₀ + Cₘ)) * A * K ^ ((r : ℝ) + (n : ℝ) / 2) := by
  rw [hparseval] at hzero
  exact twoTerm_bound_of_graded_endpoints (lt_of_lt_of_le zero_lt_one hK)
    hC hinterpolation hzero hhigh

section Hilbert

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G]

/-- Order-zero Sobolev size agrees with L² by Parseval (`app:not:fourier`),
for square-integrable periodic fields. -/
theorem periodicSobolevNorm_zero_eq_periodicL2Norm {f : Torus n → G}
    (hf : MeasureTheory.MemLp f 2) : periodicSobolevNorm 0 f = periodicL2Norm f := by
  simpa only [periodicSobolevNorm, Real.rpow_zero, one_mul] using
    (periodicL2Norm_eq_sqrt_tsum hf).symm

/-- The spectral two-term estimate in `app:lem:sharp-fourier-embedding`, with
all lattice estimates and Parseval discharged. The order-`m` energy series
is explicitly assumed summable, so the Sobolev size is a convergent sum. -/
theorem fourierInterpolation_sum_le {f : Torus n → G}
    (hf : MeasureTheory.MemLp f 2) {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K)
    (hweighted : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    Summable (fourierInterpolationTerm r f) ∧
      (∑' k, fourierInterpolationTerm r f k) ≤
        Real.sqrt ((5 : ℝ) ^ n * 2 ^ r) * K ^ ((r : ℝ) + (n : ℝ) / 2) *
          periodicL2Norm f +
        Real.sqrt (frequencyTailConstant n (2 * ((m : ℝ) - r))) *
          K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f := by
  simpa only [periodicSobolevNorm_zero_eq_periodicL2Norm hf] using
    fourierInterpolation_sum_le_of_lattice_bounds f hK
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (summable_sq_periodicFourierCoeff hf) hweighted
      (summable_besselWeight_low r K) (summable_besselWeight_high hm hK)
      (tsum_besselWeight_low_le hK) (tsum_besselWeight_high_le hm hK)

end Hilbert

/-- An explicit constant, independent of the field and cutoff, for the torus
estimate in `app:lem:sharp-fourier-embedding`. -/
def fourierInterpolationConstant (n r m : ℕ) : ℝ :=
  (((r : ℝ) + 1) * Real.sqrt 2) *
    max (Real.sqrt ((5 : ℝ) ^ n * 2 ^ r))
      (Real.sqrt (frequencyTailConstant n (2 * ((m : ℝ) - r))))

/-- Nonnegativity of the interpolation constant
(`app:lem:sharp-fourier-embedding`). -/
theorem fourierInterpolationConstant_nonneg (n r m : ℕ) :
    0 ≤ fourierInterpolationConstant n r m := by
  unfold fourierInterpolationConstant
  positivity

section Hilbert

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G]

/-- The two-term Cʳ estimate of `app:lem:sharp-fourier-embedding`, conditional
only on the exact derivative reconstruction bound. Lattice bounds and Parseval
are proved inputs; the order-`m` Fourier energy has explicit summability. -/
theorem cNorm_le_fourierInterpolation_of_reconstruction {f : Torus n → G}
    (hf : IsSmoothPeriodic f) {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K)
    (hweighted : Summable (fun k : Fin n → ℤ ↦
      (1 + frequencyNorm k ^ 2) ^ (m : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2)))
    (hinversion : Summable (fourierInterpolationTerm r f) →
      cNorm (fundamentalCell n) r (periodicLift f) ≤
        (((r : ℝ) + 1) * Real.sqrt 2) * ∑' k, fourierInterpolationTerm r f k) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      fourierInterpolationConstant n r m *
        (K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm f +
          K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f) := by
  have hmem : MeasureTheory.MemLp f 2 :=
    hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  apply cNorm_le_fourierInterpolation_of_spectral_bound f (by positivity) hK hinversion
  · simpa only [periodicSobolevNorm_zero_eq_periodicL2Norm hmem] using
      fourierInterpolation_sum_le hmem hm hK hweighted
  · exact periodicSobolevNorm_zero_eq_periodicL2Norm hmem

/-- The two-term estimate of `app:lem:sharp-fourier-embedding` on the unit torus,
with the shared Cʳ and Bessel-potential norms. The constant depends only on
`n`, `r`, and `m`. Smoothness supplies summability of the Sobolev energy, and
Fourier reconstruction supplies the Cʳ bound. -/
theorem cNorm_le_fourierInterpolation {f : Torus n → G}
    (hf : IsSmoothPeriodic f) {r m : ℕ} {K : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      fourierInterpolationConstant n r m *
        (K ^ ((r : ℝ) + (n : ℝ) / 2) * periodicL2Norm f +
          K ^ ((r : ℝ) + (n : ℝ) / 2 - m) * periodicSobolevNorm m f) := by
  apply cNorm_le_fourierInterpolation_of_reconstruction hf hm hK
    (hf.summable_periodicSobolevNorm m)
  intro hs
  exact hf.cNorm_le_fourier_majorant hs

/-- The graded-profile corollary of `app:lem:sharp-fourier-embedding` on the
unit torus. Only the Sobolev profile at orders zero and `m` is needed; all
Fourier reconstruction and summability inputs are discharged. -/
theorem cNorm_le_gradedSobolevProfile {f : Torus n → G}
    (hf : IsSmoothPeriodic f) {r m : ℕ} {K C₀ Cₘ A : ℝ}
    (hm : (r : ℝ) + (n : ℝ) / 2 < m) (hK : 1 ≤ K)
    (hzero : periodicSobolevNorm 0 f ≤ C₀ * A)
    (hhigh : periodicSobolevNorm m f ≤ Cₘ * A * K ^ (m : ℝ)) :
    cNorm (fundamentalCell n) r (periodicLift f) ≤
      (fourierInterpolationConstant n r m * (C₀ + Cₘ)) *
        A * K ^ ((r : ℝ) + (n : ℝ) / 2) := by
  have hmem : MeasureTheory.MemLp f 2 :=
    hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  exact cNorm_le_gradedSobolevProfile_of_interpolation f hK
    (fourierInterpolationConstant_nonneg n r m)
    (cNorm_le_fourierInterpolation hf hm hK)
    (periodicSobolevNorm_zero_eq_periodicL2Norm hmem) hzero hhigh

end Hilbert

end JanetCartan
