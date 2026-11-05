module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.ProductBounds.Profiles

/-!
# Actual raw auxiliary source bounds

The source multiplication step of `app:ch_background:eq:bg-Vaux-raw-band`
and `app:ch_background:eq:bg-Vaux-band`, starting from arbitrary L² data.
The squared cutoff is applied before multiplication, exactly as in `rawSource`.
-/

@[expose] public noncomputable section

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n : ℕ}

/-- The actual finite Fourier representative inherits the L² cutoff estimate.
This supplies the field profile for source multiplication in
`app:ch_background:eq:bg-Vaux-raw-band`, with no regularity of the input. -/
theorem periodicSobolevNorm_squaredCutoff_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : ℝ} (hK : 1 ≤ K) (h : PeriodicL2 n E) (s : ℕ) :
    periodicSobolevNorm s (AuxiliaryRealization.squaredCutoff K h) ≤
      Real.sqrt 5 ^ s * K ^ s * ‖h‖ := by
  have hb := RawCutoffBounds.auxiliarySquaredCutoff_band hK h s
  rw [(periodicSobolevScale n E).gradeNorm_eq
    (RawCutoffBounds.auxiliarySquaredCutoff_mem K h s)] at hb
  change periodicSobolevSeminorm s ⟨_, _⟩ ≤ _ at hb
  rw [periodicSobolevSeminorm_eq] at hb
  simpa only [periodicSobolevNorm, periodicFourierCoeff_congr_ae
    (RawCutoffBounds.auxiliarySquaredCutoff_coeFn K h)] using hb

/-- Source constant chosen using only dimension, Sobolev order and the primitive
cutoff-jet profile (`app:ch_background:eq:bg-Vaux-band`). -/
def rawSourceBandConstant (n s : ℕ) (a : ℕ → ℝ) : ℝ :=
  coefficientBandConstant n s a (fun j ↦ Real.sqrt 5 ^ j)

/-- Nonnegativity of the actual source bound's constant
(`app:ch_background:eq:bg-Vaux-band`). -/
theorem rawSourceBandConstant_nonneg (n s : ℕ) (a : ℕ → ℝ) :
    0 ≤ rawSourceBandConstant n s a :=
  coefficientBandConstant_nonneg n s a _

/-- The actual ordered source satisfies the graded raw-band estimate from
primitive cutoff jets and arbitrary L² data. Consumed by the Bessel gain and
physical assembly in `app:ch_background:eq:bg-Vaux-band`; no source or field
estimate is assumed. -/
theorem periodicSobolevNorm_rawSource_le_of_profile
    (s : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r * T ^ r)
    (h : OutputL2 n) :
    periodicSobolevNorm s (rawSource χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  exact periodicSobolevNorm_smul_le_of_profiles s a (fun j ↦ Real.sqrt 5 ^ j)
    χsrc (AuxiliaryRealization.squaredCutoff K h) hχ
    (AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h)
    hT hTK (norm_nonneg _) hcoef
    (fun j _ ↦ periodicSobolevNorm_squaredCutoff_le (hT.trans hTK) h j)

/-- The same estimate on the actual L² source class, with its canonical scale
norm. This transfers the representative estimate to the Bessel input in
`app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem gradeNorm_rawSourceL2_le_of_profile
    (s : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r * T ^ r)
    (h : OutputL2 n) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (rawSourceL2 χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  have hm : rawSourceL2 χsrc K h ∈ periodicSobolevLevel n (Euclidean n) s := by
    rw [← toL2_ofSmooth_rawSource χsrc hχ K h s]
    exact PeriodicSobolevSpace.toL2_mem _ _
  rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq hm]
  change periodicSobolevSeminorm s ⟨_, _⟩ ≤ _
  rw [periodicSobolevSeminorm_eq]
  have hb := periodicSobolevNorm_rawSource_le_of_profile s a χsrc hχ hT hTK hcoef h
  simpa only [periodicSobolevNorm, periodicFourierCoeff_congr_ae
    (rawSourceL2_coeFn χsrc K h)] using hb

/-- Fixed finite coefficient jets give the actual source bound for every
`K ≥ 1`, by taking `T = 1`. The order cap and jet profile are fixed before
choosing the cutoff or datum (`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_rawSource_le_of_fixedJets
    (S : ℕ) (a : ℕ → ℝ) (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hcoef : ∀ r ≤ S, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ a r)
    {K : ℝ} (hK : 1 ≤ K) (h : OutputL2 n) (s : ℕ) (hs : s ≤ S) :
    periodicSobolevNorm s (rawSource χsrc K h) ≤
      rawSourceBandConstant n s a * K ^ s * ‖h‖ := by
  apply periodicSobolevNorm_rawSource_le_of_profile s a χsrc hχ (T := 1)
    le_rfl hK _ h
  intro r hr
  simpa only [one_pow, mul_one] using hcoef r (hr.trans hs)

/-- The original exterior multiplier obeys the same scalar estimate as the
source cutoff, retaining its literal `1-ψ` form. This is consumed by exterior
and final-cutoff errors in `app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_exterior_smul_le_of_profiles
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : ℕ) (a b : ℕ → ℝ) (ψ : Torus n → ℝ) (f : Torus n → E)
    (hψ : IsSmoothPeriodic ψ) (hf : IsSmoothPeriodic f)
    {T K H : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K) (hH : 0 ≤ H)
    (hcoef : ∀ r ≤ s, cNorm (fundamentalCell n) r
      (periodicLift (fun x ↦ 1 - ψ x)) ≤ a r * T ^ r)
    (hfield : ∀ j ≤ s, periodicSobolevNorm j f ≤ b j * K ^ j * H) :
    periodicSobolevNorm s (fun x ↦ (1 - ψ x) • f x) ≤
      coefficientBandConstant n s a b * K ^ s * H :=
  periodicSobolevNorm_smul_le_of_profiles s a b (fun x ↦ 1 - ψ x) f
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩ hf hT hTK hH hcoef hfield

end JanetCartan.AuxiliaryRawBand
