module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Spectral
public import JanetCartan.Analysis.Fourier.Periodic.Parseval
public import JanetCartan.Analysis.Fourier.Periodic.Calculus
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Sobolev bounds for the fixed periodic cutoff

The H^r part of `main:eq:smoothing-low` is proved for `periodicCutoff`, using
its exact multiplier identity and Parseval. No kernel bound or assumed Parseval
identity is needed. The input C⁰ norm is the shared norm on the fundamental cell.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ}

/-- `main:lem:smoothing`: the fixed rescaled symbol has absolute value at most one. -/
theorem abs_periodicCutoffSymbol_le_one (R : ℝ) (k : Fin n → ℤ) :
    |periodicCutoffSymbol R k| ≤ 1 := by
  have h := fourierCutoff_mem_Icc
    ((2 * Real.pi / R) •
      (WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n)))
  exact (abs_of_nonneg h.1).trans_le h.2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:smoothing`: the C⁰ norm on the fundamental cell bounds a smooth
periodic field everywhere on the quotient torus. -/
theorem IsSmoothPeriodic.norm_le_cNorm_zero {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (x : Torus n) :
    ‖f x‖ ≤ cNorm (fundamentalCell n) 0 (periodicLift f) := by
  classical
  choose a ha using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  have hy : torusQuotient y = x := by
    funext i
    exact ha i
  have hb := norm_iteratedFDeriv_periodicLift_le f 0
    (fun z hz ↦ norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
      (hf.2.of_le (by simp)) hz (Nat.le_refl 0)) y
  simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply, hy] using hb

variable [CompleteSpace F]

/-- `main:eq:smoothing-low`: the fixed cutoff contracts every Sobolev norm whose
input energy is summable, including nonintegral orders. -/
theorem periodicSobolevNorm_periodicCutoff_le {f : Torus n → F}
    (hf : Continuous f) {R : ℝ} (hR : 0 < R) (s : ℝ)
    (hs : Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))) :
    periodicSobolevNorm s (periodicCutoff R f) ≤ periodicSobolevNorm s f := by
  simpa only [one_mul] using periodicSobolevNorm_le_of_real_multiplier
    (periodicCutoffSymbol R) (periodicFourierCoeff_periodicCutoff hf hR)
    (by norm_num : (0 : ℝ) ≤ 1) (abs_periodicCutoffSymbol_le_one R) s hs

end JanetCartan

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- `main:eq:smoothing-low`: the actual cutoff has summable Fourier energy at
every integer Sobolev order, for continuous input fields. -/
theorem summable_sobolevEnergy_periodicCutoff {f : Torus n → F}
    (hf : Continuous f) {R : ℝ} (hR : 0 < R) (r : ℕ) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (r : ℝ) *
      (‖(periodicFourierCoeff (periodicCutoff R f) k).1‖ ^ 2 +
        ‖(periodicFourierCoeff (periodicCutoff R f) k).2‖ ^ 2)) :=
  summable_sobolevEnergy_of_hasFourierSupport (hasFourierSupport_periodicCutoff hf hR)
    (hasSum_sq_periodicFourierCoeff_of_continuous
      (isSmoothPeriodic_periodicCutoff R f).1).summable r

/-- `main:eq:smoothing-low`: H^r smoothing from a pointwise bound, with explicit
constant `(√5)^r`. Parseval and the fixed multiplier identity are discharged. -/
theorem periodicSobolevNorm_periodicCutoff_le_of_bound {f : Torus n → F}
    (hf : Continuous f) {R A : ℝ} (hR : 1 ≤ R) (hA : 0 ≤ A)
    (hbound : ∀ x, ‖f x‖ ≤ A) (r : ℕ) :
    periodicSobolevNorm (r : ℝ) (periodicCutoff R f) ≤
      Real.sqrt 5 ^ r * R ^ r * A := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  simpa only [one_mul] using periodicSobolevNorm_le_scale_of_real_multiplier
    (periodicCutoffSymbol R) (periodicFourierCoeff_periodicCutoff hf hRpos)
    (by norm_num : (0 : ℝ) ≤ 1) hA hR (abs_periodicCutoffSymbol_le_one R)
    hbound (hasFourierSupport_periodicCutoff hf hRpos)
    (hasSum_sq_periodicFourierCoeff_integral
      (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))) r

/-- `main:eq:smoothing-low`: the H^r estimate for the one fixed cutoff family,
with the C⁰ size of the input measured on the closed fundamental cell. -/
theorem periodicSobolevNorm_periodicCutoff_le_cNorm_zero {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {R : ℝ} (hR : 1 ≤ R) (r : ℕ) :
    periodicSobolevNorm (r : ℝ) (periodicCutoff R f) ≤
      Real.sqrt 5 ^ r * R ^ r * cNorm (fundamentalCell n) 0 (periodicLift f) :=
  periodicSobolevNorm_periodicCutoff_le_of_bound hf.1 hR
    (cNorm_nonneg _ _ _) hf.norm_le_cNorm_zero r

end JanetCartan
