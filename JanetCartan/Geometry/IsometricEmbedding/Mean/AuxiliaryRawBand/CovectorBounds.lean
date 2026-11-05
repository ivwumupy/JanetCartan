module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.ProductBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.SmoothCovector

/-!
# Raw covector and differentiated covector profiles

The Bessel gain in `app:ch_background:eq:bg-Vaux-raw-band` cancels the
first derivative in the full strain. The constants below depend only on the
primitive source-cutoff profile, dimension and order; the datum remains L².
-/

@[expose] public noncomputable section

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n : ℕ}

private theorem norm_ofSmooth_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : ℕ) (f : Torus n → E) (hf : IsSmoothPeriodic f) :
    ‖PeriodicSobolevSpace.ofSmooth s f hf‖ = periodicSobolevNorm s f := by
  rw [PeriodicSobolevSpace.norm_eq]
  simp only [periodicSobolevNorm,
    periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _)]

private theorem sobolev_mono {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : Torus n → E} (hf : IsSmoothPeriodic f) {r s : ℕ} (hrs : r ≤ s) :
    periodicSobolevNorm r f ≤ periodicSobolevNorm s f := by
  apply Real.sqrt_le_sqrt
  apply (hf.summable_periodicSobolevNorm r).tsum_le_tsum _
    (hf.summable_periodicSobolevNorm s)
  intro k
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg (frequencyNorm k)]) (by exact_mod_cast hrs)

/-- Exact Bessel gain followed by the primitive source estimate, consumed by
the full strain in `app:ch_background:eq:bg-Vaux-band`. -/
theorem periodicSobolevNorm_rawCovector_succ_le_of_profile
    (s : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r * T ^ r)
    (h : OutputL2 n) :
    periodicSobolevNorm (s + 1) (rawCovector χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  rw [periodicSobolevNorm_rawCovector χsrc hχ]
  exact periodicSobolevNorm_rawSource_le_of_profile s a χsrc hχ hT hTK hcoef h

/-- The undifferentiated fixed covector has the same raw-band profile,
including order zero (`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_rawCovector_le_of_profile
    (s : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r * T ^ r)
    (h : OutputL2 n) :
    periodicSobolevNorm s (rawCovector χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  have hm := sobolev_mono (isSmoothPeriodic_rawCovector χsrc hχ K h) (Nat.le_succ s)
  simp only [Nat.cast_succ] at hm
  exact hm.trans
    (periodicSobolevNorm_rawCovector_succ_le_of_profile s a χsrc hχ hT hTK hcoef h)

/-- The first derivative costs no additional power of `K`, because it is
paired with the same Bessel inverse. This is the principal full-strain input
in `app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_coordinateDeriv_rawCovector_le_of_profile
    (s : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r * T ^ r)
    (h : OutputL2 n) (i : Fin n) :
    periodicSobolevNorm s (periodicCoordinateDeriv i (rawCovector χsrc K h)) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  have hd := PeriodicSobolevSpace.norm_ofSmooth_coordinateDeriv_le s i
    (rawCovector χsrc K h) (isSmoothPeriodic_rawCovector χsrc hχ K h)
  rw [norm_ofSmooth_eq, norm_ofSmooth_eq] at hd
  simp only [Nat.cast_add, Nat.cast_one] at hd
  exact hd.trans (periodicSobolevNorm_rawCovector_succ_le_of_profile
    s a χsrc hχ hT hTK hcoef h)

/-- Fixed finite jets specialize the same covector and derivative bounds at
`T=1`, for every `K ≥ 1` (`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_rawCovector_succ_le_of_fixedJets
    (S : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hcoef : ∀ r ≤ S, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r)
    {K : ℝ} (hK : 1 ≤ K) (h : OutputL2 n) (s : ℕ) (hs : s ≤ S) :
    periodicSobolevNorm (s + 1) (rawCovector χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  apply periodicSobolevNorm_rawCovector_succ_le_of_profile s a χsrc hχ
    (T := 1) le_rfl hK _ h
  intro r hr
  simpa only [one_pow, mul_one] using hcoef r (hr.trans hs)

end JanetCartan.AuxiliaryRawBand
