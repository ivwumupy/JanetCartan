module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Basic
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

/-!
# Integer Sobolev subspaces of real L²

The levels for `app:ch_background:prop:bg-inverse` are defined by actual
square summability of the weighted Fourier coefficients. Their seminorms are
pulled back from ℓ², and Parseval identifies level zero with real L².
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Actual Fourier Sobolev subspace of real L²
(`app:ch_background:prop:bg-inverse`). Membership includes convergence. -/
def periodicSobolevLevel (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (s : ℕ) :
    Submodule ℝ (PeriodicL2 n F) where
  carrier := {u | Memℓp (weightedPeriodicL2FourierCoeff s u) 2}
  zero_mem' := by
    change Memℓp (weightedPeriodicL2FourierCoeff s (0 : PeriodicL2 n F)) 2
    rw [map_zero]
    exact zero_memℓp
  add_mem' := by
    intro u v hu hv
    change Memℓp (weightedPeriodicL2FourierCoeff s (u + v)) 2
    rw [map_add]
    exact hu.add hv
  smul_mem' := by
    intro c u hu
    change Memℓp (weightedPeriodicL2FourierCoeff s (c • u)) 2
    rw [map_smul]
    exact hu.const_smul c

/-- Sobolev membership is precisely convergence of the Fourier energy in the
shared normalization (`app:not:fourier`). -/
theorem mem_periodicSobolevLevel_iff (s : ℕ) (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F s ↔
      Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
        (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2)) := by
  change Memℓp _ 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedPeriodicL2FourierCoeff_sq]

/-- Parseval identifies the zeroth Sobolev level with all of L²
(`app:not:fourier`). -/
theorem periodicSobolevLevel_zero : periodicSobolevLevel n F 0 = ⊤ := by
  apply top_unique
  intro u _
  rw [mem_periodicSobolevLevel_iff]
  simpa using summable_sq_periodicFourierCoeff (Lp.memLp u)

omit [FiniteDimensional ℝ F] in
/-- Weighted coefficients increase in norm with the order
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_weightedPeriodicL2FourierCoeff_mono {s t : ℕ} (h : s ≤ t)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    ‖weightedPeriodicL2FourierCoeff s u k‖ ≤ ‖weightedPeriodicL2FourierCoeff t u k‖ := by
  simp only [weightedPeriodicL2FourierCoeff_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (periodicSobolevWeight_pos _ _)]
  exact mul_le_mul_of_nonneg_right (periodicSobolevWeight_mono k h) (norm_nonneg _)

/-- Sobolev levels are nested (`app:ch_background:prop:bg-inverse`). -/
theorem antitone_periodicSobolevLevel : Antitone (periodicSobolevLevel n F) := by
  intro s t h u hu
  exact Memℓp.mono' hu (norm_weightedPeriodicL2FourierCoeff_mono h u)

/-- The square-summable Fourier coefficient space (`app:not:fourier`). -/
abbrev PeriodicFourierL2 (n : ℕ) (F : Type*) [NormedAddCommGroup F] : Type _ :=
  lp (fun _ : Fin n → ℤ ↦ FourierPair F) 2

/-- Weighted analysis as a genuine ℓ²-valued linear map
(`app:ch_background:prop:bg-inverse`). -/
def periodicSobolevAnalysis (s : ℕ) :
    periodicSobolevLevel n F s →ₗ[ℝ] PeriodicFourierL2 n F where
  toFun u := ⟨weightedPeriodicL2FourierCoeff s u.val, u.property⟩
  map_add' u v := by
    apply lp.ext
    exact (weightedPeriodicL2FourierCoeff s).map_add u.val v.val
  map_smul' c u := by
    apply lp.ext
    exact (weightedPeriodicL2FourierCoeff s).map_smul c u.val

/-- Evaluation of weighted ℓ² analysis (`app:not:fourier`). -/
@[simp] theorem periodicSobolevAnalysis_apply (s : ℕ)
    (u : periodicSobolevLevel n F s) (k : Fin n → ℤ) :
    periodicSobolevAnalysis s u k = weightedPeriodicL2FourierCoeff s u.val k := rfl

/-- The Sobolev seminorm pulled back from ℓ²
(`app:ch_background:prop:bg-inverse`). -/
def periodicSobolevSeminorm (s : ℕ) : Seminorm ℝ (periodicSobolevLevel n F s) :=
  (normSeminorm ℝ (PeriodicFourierL2 n F)).comp (periodicSobolevAnalysis s)

/-- The abstract seminorm agrees exactly with the shared Fourier expression;
its domain guarantees summability (`app:not:fourier`). -/
theorem periodicSobolevSeminorm_eq (s : ℕ) (u : periodicSobolevLevel n F s) :
    periodicSobolevSeminorm s u = periodicSobolevNorm s (u.val : Torus n → F) := by
  change ‖periodicSobolevAnalysis s u‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, periodicSobolevAnalysis_apply,
    norm_weightedPeriodicL2FourierCoeff_sq, periodicSobolevNorm, Real.sqrt_eq_rpow]

/-- Parseval gives the original L² norm at order zero
(`app:not:fourier`). -/
theorem periodicSobolevSeminorm_zero (u : periodicSobolevLevel n F 0) :
    periodicSobolevSeminorm 0 u = ‖u.val‖ := by
  rw [periodicSobolevSeminorm_eq]
  simp only [periodicSobolevNorm, Nat.cast_zero, Real.rpow_zero, one_mul]
  rw [← periodicL2Norm_eq_sqrt_tsum (Lp.memLp u.val), periodicL2Norm_coe]

/-- The same element's Sobolev norm is monotone in its order
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicSobolevSeminorm_mono {s t : ℕ} (h : s ≤ t)
    (u : periodicSobolevLevel n F t) :
    periodicSobolevSeminorm s ⟨u.val, antitone_periodicSobolevLevel h u.property⟩ ≤
      periodicSobolevSeminorm t u := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  exact norm_weightedPeriodicL2FourierCoeff_mono h u.val

/-- The Fourier Sobolev scale on actual real L², with the normalization used in
`app:ch_background:prop:bg-inverse`. -/
def periodicSobolevScale (n : ℕ) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] : GradedScale (PeriodicL2 n F) where
  level := periodicSobolevLevel n F
  level_zero := periodicSobolevLevel_zero
  antitone_level := antitone_periodicSobolevLevel
  seminorm := periodicSobolevSeminorm
  seminorm_zero := periodicSobolevSeminorm_zero
  monotone_seminorm := periodicSobolevSeminorm_mono

/-- Smooth periodic fields belong to every actual Sobolev level
(`app:ch_background:prop:bg-inverse`). -/
theorem IsSmoothPeriodic.toLp_mem_periodicSobolevLevel {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (s : ℕ) (hLp : MemLp f 2 volume) :
    hLp.toLp f ∈ periodicSobolevLevel n F s := by
  rw [mem_periodicSobolevLevel_iff]
  simpa only [periodicFourierCoeff_congr_ae hLp.coeFn_toLp] using
    hf.summable_periodicSobolevNorm s

/-- On every smooth representative, the scale norm equals the shared
`periodicSobolevNorm` (`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem IsSmoothPeriodic.gradeNorm_toLp {f : Torus n → F} (hf : IsSmoothPeriodic f)
    (s : ℕ) (hLp : MemLp f 2 volume) :
    (periodicSobolevScale n F).gradeNorm s (hLp.toLp f) = periodicSobolevNorm s f := by
  rw [(periodicSobolevScale n F).gradeNorm_eq (hf.toLp_mem_periodicSobolevLevel s hLp)]
  calc
    _ = periodicSobolevNorm s (hLp.toLp f) :=
      periodicSobolevSeminorm_eq s ⟨hLp.toLp f, hf.toLp_mem_periodicSobolevLevel s hLp⟩
    _ = periodicSobolevNorm s f := by
      simp only [periodicSobolevNorm, periodicFourierCoeff_congr_ae hLp.coeFn_toLp]

end JanetCartan
