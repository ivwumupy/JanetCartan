module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRealization.InputCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Scalar
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density.Coefficients
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev

/-! # Raw auxiliary cutoff bounds on actual L² classes
These are the Fourier-input estimates consumed by
`app:ch_background:eq:bg-Vaux-raw-band` and `main:eq:linear-two-errors`.
No physical source or output cutoff is inserted. -/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawCutoffBounds

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The squared auxiliary multiplier identity for arbitrary L² input,
extending `AuxiliaryRealization.periodicFourierCoeff_squaredCutoff`
(`app:ch_background:defn:bg-mixed`). -/
theorem periodicFourierCoeff_squaredCutoff_memLp {h : Torus n → F}
    (hh : MemLp h 2) {K : ℝ} (hK : 0 < K) (k : Fin n → ℤ) :
    periodicFourierCoeff (AuxiliaryRealization.squaredCutoff K h) k =
      periodicCutoffSymbol K k ^ 2 • periodicFourierCoeff h k := by
  rw [AuxiliaryRealization.squaredCutoff,
    periodicFourierCoeff_periodicCutoff (isSmoothPeriodic_periodicCutoff K h).1 hK,
    periodicFourierCoeff_periodicCutoff_memLp hh hK, smul_smul, pow_two]

/-- Actual squared raw cutoff on the existing real periodic L² space
(`app:ch_background:defn:bg-mixed`). -/
def auxiliarySquaredCutoff (K : ℝ) (h : PeriodicL2 n F) : PeriodicL2 n F :=
  ((AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h).1.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).toLp _

omit [FiniteDimensional ℝ F] in
/-- The L² operator has the original finite Fourier-sum representative
(`app:ch_background:defn:bg-mixed`). -/
theorem auxiliarySquaredCutoff_coeFn (K : ℝ) (h : PeriodicL2 n F) :
    (auxiliarySquaredCutoff K h : Torus n → F) =ᵐ[volume]
      AuxiliaryRealization.squaredCutoff K h := MemLp.coeFn_toLp _

/-- Exact coefficient identity on L² classes (`app:ch_background:defn:bg-mixed`). -/
theorem auxiliarySquaredCutoff_coeff {K : ℝ} (hK : 0 < K)
    (h : PeriodicL2 n F) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (auxiliarySquaredCutoff K h) =
      periodicCutoffSymbol K k ^ 2 • periodicL2FourierCoeff k h := by
  simp only [periodicL2FourierCoeff_apply,
    periodicFourierCoeff_congr_ae (auxiliarySquaredCutoff_coeFn K h),
    periodicFourierCoeff_squaredCutoff_memLp (Lp.memLp h) hK, WithLp.toLp_smul]

/-- Weighted-energy convergence for the cut auxiliary input at every integer
order (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem auxiliarySquaredCutoff_mem (K : ℝ) (h : PeriodicL2 n F) (s : ℕ) :
    auxiliarySquaredCutoff K h ∈ (periodicSobolevScale n F).level s :=
  (AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h).toLp_mem_periodicSobolevLevel s _

private theorem squaredSymbol_bound (K : ℝ) (k : Fin n → ℤ) :
    |periodicCutoffSymbol K k ^ 2| ≤ 1 := by
  have h := abs_periodicCutoffSymbol_le_one K k
  rw [abs_pow]
  nlinarith [abs_nonneg (periodicCutoffSymbol K k)]

/-- `app:ch_background:eq:bg-Vaux-raw-band`: the raw squared cutoff gains
integer Sobolev regularity from arbitrary L² data, with constant `(√5)^s`. -/
theorem auxiliarySquaredCutoff_band {K : ℝ} (hK : 1 ≤ K)
    (h : PeriodicL2 n F) (s : ℕ) :
    (periodicSobolevScale n F).gradeNorm s (auxiliarySquaredCutoff K h) ≤
      Real.sqrt 5 ^ s * K ^ s * ‖h‖ := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := summable_sq_periodicFourierCoeff (Lp.memLp h)
  have hs0 : Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (0 : ℝ) *
      (‖(periodicFourierCoeff h k).1‖ ^ 2 + ‖(periodicFourierCoeff h k).2‖ ^ 2)) := by
    simpa using hs
  have hc := periodicFourierCoeff_squaredCutoff_memLp (Lp.memLp h) hp
  have hb := periodicSobolevNorm_le_of_real_multiplier _ hc
    (by norm_num : (0 : ℝ) ≤ 1) (squaredSymbol_bound K) 0 hs0
  have hsum := summable_sobolevEnergy_of_real_multiplier _ hc (squaredSymbol_bound K) 0 hs0
  simp only [Real.rpow_zero, one_mul] at hsum
  have hz : periodicSobolevNorm 0 (h : Torus n → F) = ‖h‖ := by
    simpa only [periodicSobolevNorm, Real.rpow_zero, one_mul] using
      (periodicL2Norm_eq_sqrt_tsum (Lp.memLp h)).symm.trans (periodicL2Norm_coe h)
  rw [one_mul, hz] at hb
  unfold auxiliarySquaredCutoff
  rw [(AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h).gradeNorm_toLp]
  exact (periodicSobolevNorm_le_scale_of_hasFourierSupport hK
    (AuxiliaryRealization.hasFourierSupport_squaredCutoff h hp) hsum s).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))

/-- `main:eq:linear-two-errors`: decay of the auxiliary squared-cutoff tail.
Membership in the shared Sobolev scale supplies convergence of the weighted series. -/
theorem auxiliarySquaredCutoff_tail {K : ℝ} (hK : 1 ≤ K) (s : ℕ)
    (h : PeriodicL2 n F) (hh : h ∈ (periodicSobolevScale n F).level s) :
    ‖h - auxiliarySquaredCutoff K h‖ ≤
      (K ^ s)⁻¹ * (periodicSobolevScale n F).gradeNorm s h := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := (mem_periodicSobolevLevel_iff s h).mp hh
  have he (k : Fin n → ℤ) :
      ‖periodicL2FourierCoeff k (h - auxiliarySquaredCutoff K h)‖ ^ 2 ≤
        ((K ^ s)⁻¹) ^ 2 * ((1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
          (‖(periodicFourierCoeff h k).1‖ ^ 2 + ‖(periodicFourierCoeff h k).2‖ ^ 2)) := by
    have hm := squaredMask_tail_le hp (fourierCutoff_mem_Icc _) 
      (periodicCutoffSymbol_eq_one hp (k := k)) s
    rw [map_sub, auxiliarySquaredCutoff_coeff hp]
    rw [show periodicL2FourierCoeff k h - periodicCutoffSymbol K k ^ 2 •
        periodicL2FourierCoeff k h = (1 - periodicCutoffSymbol K k ^ 2) •
        periodicL2FourierCoeff k h by simp [sub_smul], norm_smul,
      Real.norm_eq_abs, mul_pow]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hm 2
    have hw : (Real.sqrt (1 + frequencyNorm k ^ 2) ^ s) ^ 2 =
        (1 + frequencyNorm k ^ 2) ^ (s : ℝ) := periodicSobolevWeight_sq s k
    rw [mul_pow, hw] at hsq
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖periodicL2FourierCoeff k h‖)
    simpa only [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2,
      mul_assoc, periodicCutoffSymbol, WithLp.fst, WithLp.snd] using this
  have hsum := (hasSum_sq_periodicL2FourierCoeff (h - auxiliarySquaredCutoff K h))
  have hb := hsum.summable.tsum_le_tsum he (hs.mul_left (((K ^ s)⁻¹) ^ 2))
  rw [hsum.tsum_eq, tsum_mul_left] at hb
  have hn : (periodicSobolevScale n F).gradeNorm s h = periodicSobolevNorm s h := by
    rw [(periodicSobolevScale n F).gradeNorm_eq hh]
    exact periodicSobolevSeminorm_eq s ⟨h, hh⟩
  rw [hn, periodicSobolevNorm]
  have ht := Real.sqrt_le_sqrt hb
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (inv_nonneg.mpr (pow_nonneg hp.le s))] using ht

private theorem l2_ext_coeff {u v : PeriodicL2 n F}
    (h : ∀ k, periodicL2FourierCoeff k u = periodicL2FourierCoeff k v) : u = v := by
  have hz : ‖u - v‖ ^ 2 = 0 := by
    rw [← (hasSum_sq_periodicL2FourierCoeff (u - v)).tsum_eq]
    simp only [map_sub, h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), tsum_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The actual auxiliary square is a bounded real linear operator on all of L²
(`app:ch_background:defn:bg-mixed`), ready for composition with the original row. -/
def auxiliarySquaredCutoffCLM {K : ℝ} (hK : 1 ≤ K) : PeriodicL2 n F →L[ℝ] PeriodicL2 n F :=
  LinearMap.mkContinuous
    { toFun := auxiliarySquaredCutoff K
      map_add' := fun u v ↦ by
        apply l2_ext_coeff
        intro k
        simp only [map_add, auxiliarySquaredCutoff_coeff (lt_of_lt_of_le zero_lt_one hK),
          smul_add]
      map_smul' := fun c u ↦ by
        apply l2_ext_coeff
        intro k
        simp only [map_smul, auxiliarySquaredCutoff_coeff (lt_of_lt_of_le zero_lt_one hK),
          RingHom.id_apply]
        exact smul_comm _ _ _ } 1 (fun h ↦ by
          simpa using auxiliarySquaredCutoff_band hK h 0)

/-- The bounded operator is the original squared Fourier cutoff
(`app:ch_background:defn:bg-mixed`). -/
@[simp] theorem auxiliarySquaredCutoffCLM_apply {K : ℝ} (hK : 1 ≤ K)
    (h : PeriodicL2 n F) : auxiliarySquaredCutoffCLM hK h = auxiliarySquaredCutoff K h := rfl

/-- Explicit summability of the weighted auxiliary energy; unlike a totalized
`tsum`, this statement records convergence (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem auxiliarySquaredCutoff_energy_summable (K : ℝ) (h : PeriodicL2 n F) (s : ℕ) :
    Summable (fun k : Fin n → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
      (‖(periodicFourierCoeff (auxiliarySquaredCutoff K h) k).1‖ ^ 2 +
        ‖(periodicFourierCoeff (auxiliarySquaredCutoff K h) k).2‖ ^ 2)) :=
  (mem_periodicSobolevLevel_iff s _).mp (auxiliarySquaredCutoff_mem K h s)

end JanetCartan.RawCutoffBounds
