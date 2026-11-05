module

public import JanetCartan.Analysis.Fourier.Periodic.Sobolev
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Fourier coefficients on real L²

Leaf definitions for the completed torus Sobolev scale used in
`app:ch_background:prop:bg-inverse`. The ambient space is real L² for the
normalized volume on the unit torus. Fourier coefficients retain both real
components, with their Hilbert product norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan

/-- Real L² on the normalized unit torus (`app:not:fourier`). -/
abbrev PeriodicL2 (n : ℕ) (F : Type*) [NormedAddCommGroup F] : Type _ :=
  Lp F 2 (volume : Measure (Torus n))

/-- The Hilbert norm on the pair of real Fourier components (`app:not:fourier`). -/
abbrev FourierPair (F : Type*) := WithLp 2 (F × F)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- Fourier coefficients are independent of the representative of an L² class
(`app:not:fourier`). -/
theorem periodicFourierCoeff_congr_ae {f g : Torus n → F} (h : f =ᵐ[volume] g)
    (k : Fin n → ℤ) : periodicFourierCoeff f k = periodicFourierCoeff g k := by
  apply Prod.ext <;> apply integral_congr_ae <;>
    filter_upwards [h] with x hx <;> simp only [hx]

omit [FiniteDimensional ℝ F] in
private theorem integrable_fourier_re (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).re • u x) :=
  ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)

omit [FiniteDimensional ℝ F] in
private theorem integrable_fourier_im (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).im • u x) :=
  ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)

/-- The Fourier coefficient map on actual real L² classes (`app:not:fourier`). -/
def periodicL2FourierCoeff (k : Fin n → ℤ) : PeriodicL2 n F →ₗ[ℝ] FourierPair F where
  toFun u := WithLp.toLp 2 (periodicFourierCoeff u k)
  map_add' u v := by
    rw [periodicFourierCoeff_congr_ae (Lp.coeFn_add u v)]
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    apply Prod.ext
    · exact (by simpa [periodicFourierCoeff, smul_add] using
        integral_add (integrable_fourier_re u k) (integrable_fourier_re v k))
    · exact (by simpa [periodicFourierCoeff, smul_add] using
        integral_add (integrable_fourier_im u k) (integrable_fourier_im v k))
  map_smul' c u := by
    rw [periodicFourierCoeff_congr_ae (Lp.coeFn_smul c u)]
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    apply Prod.ext <;>
      simp [periodicFourierCoeff, Pi.smul_apply, smul_comm _ c,
        integral_smul, RingHom.id_apply]

omit [FiniteDimensional ℝ F] in
/-- The coefficient map agrees with the representative formula (`app:not:fourier`). -/
@[simp] theorem periodicL2FourierCoeff_apply (k : Fin n → ℤ) (u : PeriodicL2 n F) :
    periodicL2FourierCoeff k u = WithLp.toLp 2 (periodicFourierCoeff u k) := rfl

omit [FiniteDimensional ℝ F] in
/-- The real L² norm agrees with the periodic integral norm (`app:not:fourier`). -/
theorem periodicL2Norm_coe (u : PeriodicL2 n F) : periodicL2Norm u = ‖u‖ := by
  have h : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) u u).symm
  rw [periodicL2Norm, h, Real.sqrt_sq (norm_nonneg u)]

/-- Parseval for real L² classes, including convergence (`app:not:fourier`). -/
theorem hasSum_sq_periodicL2FourierCoeff (u : PeriodicL2 n F) :
    HasSum (fun k ↦ ‖periodicL2FourierCoeff k u‖ ^ 2) (‖u‖ ^ 2) := by
  simpa [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2,
    periodicL2Norm_coe] using
    hasSum_sq_periodicFourierCoeff (Lp.memLp u)

/-- Bessel's bound makes each coefficient a bounded functional
(`app:not:fourier`). -/
theorem norm_periodicL2FourierCoeff_le (k : Fin n → ℤ) (u : PeriodicL2 n F) :
    ‖periodicL2FourierCoeff k u‖ ≤ ‖u‖ := by
  have h := (hasSum_sq_periodicL2FourierCoeff u).summable.le_tsum k
    (fun j _ ↦ sq_nonneg ‖periodicL2FourierCoeff j u‖)
  rw [(hasSum_sq_periodicL2FourierCoeff u).tsum_eq] at h
  nlinarith [norm_nonneg (periodicL2FourierCoeff k u), norm_nonneg u]

/-- Continuous coefficient evaluation on real L² (`app:not:fourier`). -/
def periodicL2FourierCoeffCLM (k : Fin n → ℤ) : PeriodicL2 n F →L[ℝ] FourierPair F :=
  (periodicL2FourierCoeff k).mkContinuous 1 (by
    intro u
    simpa only [one_mul] using norm_periodicL2FourierCoeff_le k u)

/-- The multiplier whose square is the integer Bessel weight
(`app:ch_background:prop:bg-inverse`). -/
def periodicSobolevWeight (s : ℕ) (k : Fin n → ℤ) : ℝ :=
  Real.sqrt (1 + frequencyNorm k ^ 2) ^ s

/-- Positivity of the Sobolev multiplier (`app:ch_background:prop:bg-inverse`). -/
theorem periodicSobolevWeight_pos (s : ℕ) (k : Fin n → ℤ) :
    0 < periodicSobolevWeight s k := by
  unfold periodicSobolevWeight
  positivity

/-- The squared multiplier is exactly the shared Fourier weight
(`app:not:fourier`). -/
theorem periodicSobolevWeight_sq (s : ℕ) (k : Fin n → ℤ) :
    periodicSobolevWeight s k ^ 2 = (1 + frequencyNorm k ^ 2) ^ (s : ℝ) := by
  rw [periodicSobolevWeight, ← pow_mul, Nat.mul_comm, pow_mul,
    Real.sq_sqrt (by positivity), Real.rpow_natCast]

/-- Monotonicity of integer Sobolev multipliers
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicSobolevWeight_mono (k : Fin n → ℤ) :
    Monotone (fun s ↦ periodicSobolevWeight s k) := by
  intro s t h
  apply pow_le_pow_right₀ _ h
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (frequencyNorm k)])

/-- Weighted Fourier analysis, prior to its restriction to square-summable
sequences (`app:ch_background:prop:bg-inverse`). -/
def weightedPeriodicL2FourierCoeff (s : ℕ) :
    PeriodicL2 n F →ₗ[ℝ] ((Fin n → ℤ) → FourierPair F) :=
  LinearMap.pi (fun k ↦ periodicSobolevWeight s k • periodicL2FourierCoeff k)

omit [FiniteDimensional ℝ F] in
/-- Pointwise weighted analysis formula (`app:not:fourier`). -/
@[simp] theorem weightedPeriodicL2FourierCoeff_apply (s : ℕ)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    weightedPeriodicL2FourierCoeff s u k =
      periodicSobolevWeight s k • periodicL2FourierCoeff k u := rfl

omit [FiniteDimensional ℝ F] in
/-- Weighted coefficient energy agrees with the original Fourier formula
(`app:not:fourier`). -/
theorem norm_weightedPeriodicL2FourierCoeff_sq (s : ℕ) (u : PeriodicL2 n F)
    (k : Fin n → ℤ) :
    ‖weightedPeriodicL2FourierCoeff s u k‖ ^ 2 =
      (1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
        (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2) := by
  rw [weightedPeriodicL2FourierCoeff_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, periodicSobolevWeight_sq, periodicL2FourierCoeff_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  rfl

end JanetCartan
