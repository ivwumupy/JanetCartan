module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Geometry

/-!
# The fixed physical field from primitive raising coefficients

The coefficient profile is an input from `jc-current-coefficient-scale`.
Pointwise agreement identifies it with the literal half tangent lift; the
bounds in `app:ch_background:eq:bg-Vaux-band` are then deduced from the actual
ordered raw source. No field estimate or inverse regularity is assumed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n N : ℕ}

/-- The actual covector-raising coefficient `½ dG g_G⁻¹` of
`app:ch_background:eq:bg-Vaux`, expressed on the real Hilbert fiber. -/
def halfTangentCoefficient (G : Euclidean n → Euclidean N) (x : Euclidean n) :
    Euclidean n →L[ℝ] Euclidean N :=
  (1 / 2 : ℝ) • ∑ i, ∑ j,
    ((inducedMetric G x)⁻¹ i j • PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j).smulRight
      (partialDeriv G x i)

/-- The coefficient is the literal half lift, for every covector
(`app:ch_background:eq:bg-Vaux`). -/
theorem halfTangentCoefficient_apply (G : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (x : Euclidean n) :
    halfTangentCoefficient G x (u x) = AuxiliaryRealization.tangentialField G u x := by
  simp only [halfTangentCoefficient, smul_apply,
    sum_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.proj_apply, smul_eq_mul, AuxiliaryRealization.tangentialField,
    Pi.smul_apply, tangentLift]

/-- Periodic extension of the very same physical field, using the primitive
raising coefficient and final cutoff (`app:ch_background:eq:bg-Vaux`). -/
def periodicField (A : Torus n → Euclidean n →L[ℝ] Euclidean N)
    (χout : Torus n → ℝ) (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    Torus n → Euclidean N :=
  fun x ↦ χout x • A x (rawCovector χsrc K h x)

/-- Smoothness of the periodic field, independently of the Sobolev order
(`app:ch_background:eq:bg-Vaux`). -/
theorem isSmoothPeriodic_periodicField
    (A : Torus n → Euclidean n →L[ℝ] Euclidean N) (hA : IsSmoothPeriodic A)
    (χout : Torus n → ℝ) (hout : IsSmoothPeriodic χout)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) : IsSmoothPeriodic (periodicField A χout χsrc K h) := by
  have hu := isSmoothPeriodic_rawCovector χsrc hsrc K h
  exact ⟨hout.1.smul (hA.1.clm_apply hu.1), hout.2.smul (hA.2.clm_apply hu.2)⟩

/-- Literal chart identity with the field fixed in `Source.lean`. Agreement is
required only where the final cutoff is nonzero, on the stated physical set
(`app:ch_background:eq:bg-Vaux`). -/
theorem physicalField_eq_periodicField
    (G : Euclidean n → Euclidean N) (W : Set (Euclidean n))
    (A : Torus n → Euclidean n →L[ℝ] Euclidean N) (χout : Torus n → ℝ)
    (hA : ∀ x ∈ W, χout (torusQuotient x) ≠ 0 →
      A (torusQuotient x) = halfTangentCoefficient G x)
    (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    EqOn (physicalField G (periodicLift χout) χsrc K h)
      (periodicLift (periodicField A χout χsrc K h)) W := by
  intro x hx
  by_cases hz : χout (torusQuotient x) = 0
  · simp [physicalField, periodicField, periodicLift, hz]
  · change _ = χout (torusQuotient x) • A (torusQuotient x)
      (periodicLift (rawCovector χsrc K h) x)
    rw [hA x hx hz, halfTangentCoefficient_apply]
    rfl

/-- Field constant determined before scales, coefficients and raw data in
`app:ch_background:eq:bg-Vaux-band`. The three profiles describe raising,
final cutoff and source cutoff, respectively. -/
def rawFieldBandConstant (n s : ℕ) (aRaise aOut aSrc : ℕ → ℝ) : ℝ :=
  coefficientBandConstant n s aOut
    (fun j ↦ coefficientBandConstant n j aRaise (fun l ↦ rawSourceBandConstant n l aSrc))

/-- Nonnegativity of the field constant (`app:ch_background:eq:bg-Vaux-band`). -/
theorem rawFieldBandConstant_nonneg (n s : ℕ) (aRaise aOut aSrc : ℕ → ℝ) :
    0 ≤ rawFieldBandConstant n s aRaise aOut aSrc :=
  coefficientBandConstant_nonneg _ _ _ _

/-- The actual ordered field obeys the graded raw-band estimate from primitive
raising and cutoff jets. The Bessel covector is fixed once for every order
(`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_periodicField_le_of_profiles
    (s : ℕ) (aRaise aOut aSrc : ℕ → ℝ)
    (A : Torus n → Euclidean n →L[ℝ] Euclidean N) (hA : IsSmoothPeriodic A)
    (χout : Torus n → ℝ) (hout : IsSmoothPeriodic χout)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hRaise : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift A) ≤ aRaise r * T ^ r)
    (hOut : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χout) ≤ aOut r * T ^ r)
    (hSrc : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ aSrc r * T ^ r)
    (h : OutputL2 n) :
    periodicSobolevNorm s (periodicField A χout χsrc K h) ≤
      rawFieldBandConstant n s aRaise aOut aSrc * K ^ s * ‖h‖ := by
  have hu := isSmoothPeriodic_rawCovector χsrc hsrc K h
  apply periodicSobolevNorm_smul_le_of_profiles s aOut _ χout _ hout
    ⟨hA.1.clm_apply hu.1, hA.2.clm_apply hu.2⟩ hT hTK (norm_nonneg _) hOut
  intro j hj
  apply periodicSobolevNorm_clm_apply_le_of_profiles j aRaise
    (fun l ↦ rawSourceBandConstant n l aSrc) A _ hA hu hT hTK (norm_nonneg _)
    (fun r hr ↦ hRaise r (hr.trans hj))
  intro l hl
  exact periodicSobolevNorm_rawCovector_le_of_profile l aSrc χsrc hsrc hT hTK
    (fun r hr ↦ hSrc r (hr.trans (hl.trans hj))) h

/-- Bounded jets at finitely many orders specialize the same field bound to
all `K ≥ 1` (`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_periodicField_le_of_fixedJets
    (S : ℕ) (aRaise aOut aSrc : ℕ → ℝ)
    (A : Torus n → Euclidean n →L[ℝ] Euclidean N) (hA : IsSmoothPeriodic A)
    (χout : Torus n → ℝ) (hout : IsSmoothPeriodic χout)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hRaise : ∀ r ≤ S, cNorm (fundamentalCell n) r (periodicLift A) ≤ aRaise r)
    (hOut : ∀ r ≤ S, cNorm (fundamentalCell n) r (periodicLift χout) ≤ aOut r)
    (hSrc : ∀ r ≤ S, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ aSrc r)
    {K : ℝ} (hK : 1 ≤ K) (h : OutputL2 n) (s : ℕ) (hs : s ≤ S) :
    periodicSobolevNorm s (periodicField A χout χsrc K h) ≤
      rawFieldBandConstant n s aRaise aOut aSrc * K ^ s * ‖h‖ := by
  apply periodicSobolevNorm_periodicField_le_of_profiles s aRaise aOut aSrc
    A hA χout hout χsrc hsrc (T := 1) le_rfl hK
    (fun r hr ↦ by simpa using hRaise r (hr.trans hs))
    (fun r hr ↦ by simpa using hOut r (hr.trans hs))
    (fun r hr ↦ by simpa using hSrc r (hr.trans hs)) h

/-- Specialization of the SAME field to the original augmented row. Only the
L² norm of `Q₀` is used; the actual inverse is supplied by
`jc-continuum-l2-inverse` (`app:ch_background:eq:bg-Vaux-band`). -/
theorem periodicSobolevNorm_periodicField_imageAdjoint_Q0_le
    {ι : Type*} [Fintype ι]
    (s : ℕ) (aRaise aOut aSrc : ℕ → ℝ)
    (A : Torus n → Euclidean n →L[ℝ] Euclidean N) (hA : IsSmoothPeriodic A)
    (χout : Torus n → ℝ) (hout : IsSmoothPeriodic χout)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    {T K : ℝ} (hT : 1 ≤ T) (hTK : T ≤ K)
    (hRaise : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift A) ≤ aRaise r * T ^ r)
    (hOut : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χout) ≤ aOut r * T ^ r)
    (hSrc : ∀ r ≤ s, cNorm (fundamentalCell n) r (periodicLift χsrc) ≤ aSrc r * T ^ r)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas ψ : C(Torus n, ℝ))
    (carriers : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q0 : OutputL2 n →L[ℝ] OutputL2 n) (e : OutputL2 n) :
    periodicSobolevNorm s (periodicField A χout χsrc K
      ((imageChannel c χmeas χsrc).adjoint (Q0 e))) ≤
      (rawFieldBandConstant n s aRaise aOut aSrc *
        ‖augmentedRow (imageChannel c χmeas χsrc) carriers ψ‖ * ‖Q0‖) * K ^ s * ‖e‖ := by
  apply (periodicSobolevNorm_periodicField_le_of_profiles s aRaise aOut aSrc
    A hA χout hout χsrc hsrc hT hTK hRaise hOut hSrc _).trans
  calc
    _ ≤ rawFieldBandConstant n s aRaise aOut aSrc * K ^ s *
        (‖augmentedRow (imageChannel c χmeas χsrc) carriers ψ‖ * ‖Q0‖ * ‖e‖) :=
      mul_le_mul_of_nonneg_left (norm_imageAdjoint_Q0_le _ carriers ψ Q0 e)
        (mul_nonneg (rawFieldBandConstant_nonneg _ _ _ _ _)
          (pow_nonneg (zero_le_one.trans (hT.trans hTK)) _))
    _ = _ := by ring

end JanetCartan.AuxiliaryRawBand
