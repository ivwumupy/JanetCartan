module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Complete

/-!
# Translation on the real periodic L² space

The translations used in the order-one difference-quotient argument of
`app:ch_background:prop:bg-inverse` act on actual equivalence classes for
normalized torus volume. The Fourier formula uses the shared real-pair convention.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Translation by `a`, acting isometrically on normalized torus L²
(`app:ch_background:prop:bg-inverse`). -/
def periodicL2Translation (a : Torus n) : PeriodicL2 n F →ₗᵢ[ℝ] PeriodicL2 n F :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ x + a) (measurePreserving_add_right volume a)

/-- Translation of representatives, almost everywhere
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicL2Translation_coe (a : Torus n) (u : PeriodicL2 n F) :
    periodicL2Translation a u =ᵐ[volume] fun x ↦ u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

/-- Translations preserve the L² norm (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem norm_periodicL2Translation (a : Torus n) (u : PeriodicL2 n F) :
    ‖periodicL2Translation a u‖ = ‖u‖ :=
  (periodicL2Translation a).norm_map u

/-- The zero translation is the identity (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem periodicL2Translation_zero (u : PeriodicL2 n F) :
    periodicL2Translation 0 u = u := by
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe 0 u] with x hx
  simpa using hx

/-- Composition of translations (`app:ch_background:prop:bg-inverse`). -/
theorem periodicL2Translation_add (a b : Torus n) (u : PeriodicL2 n F) :
    periodicL2Translation (a + b) u = periodicL2Translation a (periodicL2Translation b u) := by
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe (a + b) u,
    periodicL2Translation_coe a (periodicL2Translation b u),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      (periodicL2Translation_coe b u)] with x h₁ h₂ h₃
  simp only [h₁, h₂, h₃, add_assoc]

/-- Translation is a surjective real linear isometry, with inverse translation by
`-a` (`app:ch_background:prop:bg-inverse`). -/
def periodicL2TranslationEquiv (a : Torus n) : PeriodicL2 n F ≃ₗᵢ[ℝ] PeriodicL2 n F where
  toFun := periodicL2Translation a
  invFun := periodicL2Translation (-a)
  left_inv u := by rw [← periodicL2Translation_add, neg_add_cancel, periodicL2Translation_zero]
  right_inv u := by rw [← periodicL2Translation_add, add_neg_cancel, periodicL2Translation_zero]
  map_add' := (periodicL2Translation a).map_add
  map_smul' := (periodicL2Translation a).map_smul
  norm_map' := (periodicL2Translation a).norm_map

/-- Complex multiplication expressed on the real Hilbert pair of Fourier components
(`app:not:fourier`). -/
def fourierPairMul (z : ℂ) (v : FourierPair F) : FourierPair F :=
  WithLp.toLp 2 (z.re • v.ofLp.1 - z.im • v.ofLp.2,
    z.im • v.ofLp.1 + z.re • v.ofLp.2)

/-- Multiplication of a Fourier pair scales its squared Hilbert norm by the squared
complex modulus (`app:not:fourier`). -/
theorem norm_fourierPairMul_sq (z : ℂ) (v : FourierPair F) :
    ‖fourierPairMul z v‖ ^ 2 = ‖z‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 v]
  change ‖z.re • v.ofLp.1 - z.im • v.ofLp.2‖ ^ 2 +
    ‖z.im • v.ofLp.1 + z.re • v.ofLp.2‖ ^ 2 =
    ‖z‖ ^ 2 * (‖v.ofLp.1‖ ^ 2 + ‖v.ofLp.2‖ ^ 2)
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Complex multiplication scales the Hilbert-pair norm by its modulus
(`app:not:fourier`). -/
theorem norm_fourierPairMul (z : ℂ) (v : FourierPair F) :
    ‖fourierPairMul z v‖ = ‖z‖ * ‖v‖ := by
  have h := norm_fourierPairMul_sq z v
  nlinarith [norm_nonneg (fourierPairMul z v), mul_nonneg (norm_nonneg z) (norm_nonneg v)]

/-- Subtracting the identity multiplier on Fourier pairs (`app:not:fourier`). -/
theorem fourierPairMul_sub_one (z : ℂ) (v : FourierPair F) :
    fourierPairMul (z - 1) v = fourierPairMul z v - v := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [fourierPairMul, sub_smul] <;> module

/-- The coordinate translation vector on the unit torus
(`app:ch_background:prop:bg-inverse`). -/
def periodicCoordinateShift (i : Fin n) (h : ℝ) : Torus n :=
  Pi.single i (h : AddCircle (1 : ℝ))

/-- The coordinate translation character has physical frequency `2π kᵢ`
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicFourierCharacter_coordinateShift (k : Fin n → ℤ) (i : Fin n) (h : ℝ) :
    UnitAddTorus.mFourier k (periodicCoordinateShift i h) =
      Complex.exp (2 * Real.pi * Complex.I * (k i : ℂ) * h) := by
  classical
  have hs : UnitAddTorus.mFourier k (periodicCoordinateShift i h) =
      fourier (k i) (h : AddCircle (1 : ℝ)) := by
    change (∏ j, fourier (k j) ((Pi.single i (h : AddCircle (1 : ℝ)) : Torus n) j)) = _
    rw [Finset.prod_eq_single i]
    · simp only [Pi.single_eq_same]
    · intro j _ hj
      simp only [Pi.single_eq_of_ne hj, fourier_eval_zero]
    · simp
  rw [hs, fourier_coe_apply]
  simp

/-- Coordinate difference quotient on actual L² classes. For nonzero `h` this is
`(u(· + h eᵢ) - u) / h` (`app:ch_background:prop:bg-inverse`). -/
def periodicL2DifferenceQuotient (i : Fin n) (h : ℝ) : PeriodicL2 n F →L[ℝ] PeriodicL2 n F :=
  h⁻¹ • ((periodicL2Translation (periodicCoordinateShift i h)).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (PeriodicL2 n F))

/-- Difference quotients agree with the pointwise formula almost everywhere
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicL2DifferenceQuotient_coe (i : Fin n) (h : ℝ) (u : PeriodicL2 n F) :
    periodicL2DifferenceQuotient i h u =ᵐ[volume]
      fun x ↦ h⁻¹ • (u (x + periodicCoordinateShift i h) - u x) := by
  change (h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h) u - u) :
    PeriodicL2 n F) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul h⁻¹ (periodicL2Translation (periodicCoordinateShift i h) u - u),
    Lp.coeFn_sub (periodicL2Translation (periodicCoordinateShift i h) u) u,
    periodicL2Translation_coe (periodicCoordinateShift i h) u] with x h₁ h₂ h₃
  simp only [Pi.smul_apply, Pi.sub_apply] at h₁ h₂
  rw [h₁, h₂, h₃]

/-- Translation of the real-pair integral coefficients of an L² representative
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicFourierCoeff_translate (a : Torus n) (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    periodicFourierCoeff (fun x ↦ u (x + a)) k =
      ((UnitAddTorus.mFourier k a).re • (periodicFourierCoeff u k).1 -
        (UnitAddTorus.mFourier k a).im • (periodicFourierCoeff u k).2,
       (UnitAddTorus.mFourier k a).im • (periodicFourierCoeff u k).1 +
        (UnitAddTorus.mFourier k a).re • (periodicFourierCoeff u k).2) := by
  have hr : Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).re • u x) :=
    ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  have hi : Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).im • u x) :=
    ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  have hchar (x : Torus n) : UnitAddTorus.mFourier (-k) (x - a) =
      UnitAddTorus.mFourier k a * UnitAddTorus.mFourier (-k) x := by
    rw [sub_eq_add_neg, periodicFourierCharacter_add, mul_comm]
    congr 1
    simp [UnitAddTorus.mFourier, fourier_apply]
  apply Prod.ext
  · change (∫ x, (UnitAddTorus.mFourier (-k) x).re • u (x + a)) = _
    rw [← integral_sub_right_eq_self (μ := volume) (fun x ↦
      (UnitAddTorus.mFourier (-k) x).re • u (x + a)) a]
    simp only [sub_add_cancel, hchar, Complex.mul_re, sub_smul, mul_smul]
    simpa only [periodicFourierCoeff, Pi.smul_apply, integral_smul] using
      integral_sub (hr.smul (UnitAddTorus.mFourier k a).re) (hi.smul (UnitAddTorus.mFourier k a).im)
  · change (∫ x, (UnitAddTorus.mFourier (-k) x).im • u (x + a)) = _
    rw [← integral_sub_right_eq_self (μ := volume) (fun x ↦
      (UnitAddTorus.mFourier (-k) x).im • u (x + a)) a]
    simp only [sub_add_cancel, hchar, Complex.mul_im, add_smul, mul_smul]
    simpa only [periodicFourierCoeff, Pi.smul_apply, integral_smul, add_comm] using
      integral_add (hi.smul (UnitAddTorus.mFourier k a).re) (hr.smul (UnitAddTorus.mFourier k a).im)

/-- Fourier translation identity on actual L² classes in the shared real-pair
convention (`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicL2FourierCoeff_translation (a : Torus n) (u : PeriodicL2 n F)
    (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (periodicL2Translation a u) =
      fourierPairMul (UnitAddTorus.mFourier k a) (periodicL2FourierCoeff k u) := by
  rw [periodicL2FourierCoeff_apply,
    periodicFourierCoeff_congr_ae (periodicL2Translation_coe a u),
    periodicFourierCoeff_translate]
  rfl

/-- The Fourier multiplier of a coordinate difference quotient
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicL2FourierCoeff_differenceQuotient (i : Fin n) (h : ℝ)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (periodicL2DifferenceQuotient i h u) =
      h⁻¹ • fourierPairMul (UnitAddTorus.mFourier k (periodicCoordinateShift i h) - 1)
        (periodicL2FourierCoeff k u) := by
  change periodicL2FourierCoeff k
    (h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h) u - u)) = _
  rw [map_smul, map_sub, periodicL2FourierCoeff_translation, fourierPairMul_sub_one]

/-- The exact coefficient norm of a coordinate difference quotient, with the
physical unit-torus frequency (`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicL2FourierCoeff_differenceQuotient (i : Fin n) (h : ℝ)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    ‖periodicL2FourierCoeff k (periodicL2DifferenceQuotient i h u)‖ =
      |h|⁻¹ * ‖Complex.exp (2 * Real.pi * Complex.I * (k i : ℂ) * h) - 1‖ *
        ‖periodicL2FourierCoeff k u‖ := by
  simp only [periodicL2FourierCoeff_differenceQuotient, norm_smul, norm_fourierPairMul,
    Real.norm_eq_abs, abs_inv, periodicFourierCharacter_coordinateShift, mul_assoc]

/-- A common bound for all small nonzero coordinate difference quotients.
This is the hypothesis used to recover weighted summability in
`app:ch_background:prop:bg-inverse`. -/
def HasBoundedPeriodicDifferenceQuotients (u : PeriodicL2 n F) (C : ℝ) : Prop :=
  ∀ (i : Fin n) (h : ℝ), 0 < |h| → |h| ≤ 1 → ‖periodicL2DifferenceQuotient i h u‖ ≤ C

end JanetCartan
