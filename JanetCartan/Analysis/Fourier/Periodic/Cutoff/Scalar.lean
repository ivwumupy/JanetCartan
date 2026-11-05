module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Scalar coefficient identities for the cutoff in `main:lem:smoothing` -/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

namespace JanetCartan

variable {n : ℕ}

private theorem haar_unit_eq_volume :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm

/-- On the unit torus, Mathlib's normalized measure agrees with the shared volume
(Appendix B). -/
theorem mFourierCoeff_eq_volume_integral (f : Torus n → ℂ) (k : Fin n → ℤ) :
    mFourierCoeff f k = ∫ x : Torus n, mFourier (-k) x * f x := by
  unfold mFourierCoeff
  change (∫ x, mFourier (-k) x * f x ∂Measure.pi
    (fun _ : Fin n ↦ AddCircle.haarAddCircle)) = _
  simp only [haar_unit_eq_volume]
  rfl

/-- Negation preserves the finite summation box (Appendix B). -/
@[simp] theorem neg_mem_periodicCutoffBox (R : ℝ) (k : Fin n → ℤ) :
    -k ∈ periodicCutoffBox n R ↔ k ∈ periodicCutoffBox n R := by
  simp only [periodicCutoffBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply]
  constructor <;> intro h i <;> specialize h i <;> omega

/-- Complex encoding of the shared real coefficient pair (Appendix B). -/
theorem mFourierCoeff_ofReal {f : Torus n → ℝ} (hf : Continuous f) (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) k =
      ⟨(periodicFourierCoeff f k).1, (periodicFourierCoeff f k).2⟩ := by
  have hi : Integrable (fun x ↦ mFourier (-k) x * (f x : ℂ)) :=
    ((mFourier (-k)).continuous.mul
      (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · simpa [mFourierCoeff_eq_volume_integral, periodicFourierCoeff, Complex.mul_re]
      using (integral_re hi).symm
  · simpa [mFourierCoeff_eq_volume_integral, periodicFourierCoeff, Complex.mul_im]
      using (integral_im hi).symm

private theorem coeff_conj_ofReal (f : Torus n → ℝ) (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) (-k) =
      conj (mFourierCoeff (fun x ↦ (f x : ℂ)) k) := by
  simp only [mFourierCoeff, smul_eq_mul, ← integral_conj, map_mul,
    Complex.conj_ofReal, ← mFourier_neg, neg_neg]

private theorem integral_character_mul (k l : Fin n → ℤ) :
    (∫ x : Torus n, mFourier (-k) x * mFourier l x) = if k = l then 1 else 0 := by
  rw [← mFourierCoeff_eq_volume_integral]
  simpa only [mFourierCoeff, ContinuousMap.inner_toLp, ← mFourier_neg,
    smul_eq_mul, mul_comm] using
    (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin n))) k l

/-- Orthogonality computes the coefficients of a finite Fourier sum (Appendix B). -/
theorem mFourierCoeff_finset_sum (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ)
    (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ ∑ l ∈ s, a l * mFourier l x) k =
      if k ∈ s then a k else 0 := by
  classical
  simp only [mFourierCoeff_eq_volume_integral, Finset.mul_sum]
  rw [integral_finsetSum]
  swap
  · intro l _
    exact ((mFourier (-k)).continuous.mul
      (continuous_const.mul (mFourier l).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have ht (l : Fin n → ℤ) :
      (∫ x : Torus n, mFourier (-k) x * (a l * mFourier l x)) =
        if k = l then a l else 0 := by
    simp_rw [mul_left_comm (mFourier (-k) _) (a l)]
    rw [integral_const_mul, integral_character_mul]
    split_ifs <;> simp
  simp_rw [ht]
  by_cases hk : k ∈ s
  · rw [ite_eq_left hk, Finset.sum_eq_single k]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · exact fun h ↦ (h hk).elim
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro l hl
    rw [ite_eq_right (by intro h; exact hk (h ▸ hl))]

private theorem conjugate_sum (s : Finset (Fin n → ℤ))
    (hs : ∀ k, -k ∈ s ↔ k ∈ s) (a : (Fin n → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = conj (a k)) (x : Torus n) :
    conj (∑ k ∈ s, a k * mFourier k x) = ∑ k ∈ s, a k * mFourier k x := by
  classical
  simp only [map_sum, map_mul, ← mFourier_neg, ← ha]
  apply Finset.sum_bij (fun k _ ↦ -k)
  · intro k hk; exact (hs k).2 hk
  · intro k _ l _ h; exact neg_injective h
  · intro k hk; exact ⟨-k, (hs k).2 hk, neg_neg k⟩
  · intro k _; rfl

/-- The real sum is literally the usual complex multiplier, with zero imaginary part.
This proves preservation of reality for `main:lem:smoothing`. -/
theorem ofReal_periodicCutoff {f : Torus n → ℝ} (hf : Continuous f) (R : ℝ) (x : Torus n) :
    Complex.ofReal (periodicCutoff R f x) = ∑ k ∈ periodicCutoffBox n R,
      (periodicCutoffSymbol R k : ℂ) *
        mFourierCoeff (fun y ↦ (f y : ℂ)) k * mFourier k x := by
  have hc := conjugate_sum (periodicCutoffBox n R) (neg_mem_periodicCutoffBox R)
    (fun k ↦ (periodicCutoffSymbol R k : ℂ) * mFourierCoeff (fun y ↦ (f y : ℂ)) k)
    (by intro k; simp [periodicCutoffSymbol_neg, coeff_conj_ofReal]) x
  apply Complex.ext
  · simp [periodicCutoff, periodicFourierMode, mFourierCoeff_ofReal hf,
      Complex.mul_re, Complex.mul_im, mul_sub, mul_assoc, mul_comm]
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The scalar multiplier has exactly the prescribed Fourier coefficients
(`main:lem:smoothing`). -/
theorem mFourierCoeff_periodicCutoff {f : Torus n → ℝ} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ Complex.ofReal (periodicCutoff R f x)) k =
      (periodicCutoffSymbol R k : ℂ) * mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  simp_rw [ofReal_periodicCutoff hf]
  rw [mFourierCoeff_finset_sum]
  split_ifs with hk
  · rfl
  · rw [periodicCutoffSymbol_eq_zero_of_notMem hR hk, Complex.ofReal_zero, zero_mul]

/-- The coefficient identity in the shared real-pair notation (`main:lem:smoothing`). -/
theorem periodicFourierCoeff_periodicCutoff_scalar {f : Torus n → ℝ} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCutoff R f) k =
      periodicCutoffSymbol R k • periodicFourierCoeff f k := by
  have h := mFourierCoeff_periodicCutoff hf hR k
  rw [mFourierCoeff_ofReal (isSmoothPeriodic_periodicCutoff R f).1,
    mFourierCoeff_ofReal hf] at h
  apply Prod.ext
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

/-- Exact reproduction of scalar fields supported below the inner plateau
(`main:lem:smoothing`). -/
theorem periodicCutoff_eq_self_scalar {f : Torus n → ℝ} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (hs : HasFourierSupport R f) : periodicCutoff R f = f := by
  let g : C(Torus n, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hz (k : Fin n → ℤ) (hk : R < frequencyNorm k) : mFourierCoeff g k = 0 := by
    change mFourierCoeff (fun x ↦ (f x : ℂ)) k = 0
    rw [mFourierCoeff_ofReal hf, hs k hk]
    rfl
  have hzero : ∀ k ∉ periodicCutoffBox n R, mFourierCoeff g k = 0 := by
    intro k hk
    apply hz
    have := lt_of_not_ge (fun h ↦ hk (mem_periodicCutoffBox h))
    linarith
  have hsum : Summable (mFourierCoeff g) := summable_of_ne_finset_zero hzero
  funext x
  apply Complex.ofReal_injective
  rw [ofReal_periodicCutoff hf]
  have he := (hasSum_mFourier_series_apply_of_summable hsum x).tsum_eq
  rw [tsum_eq_sum (s := periodicCutoffBox n R) (fun k hk ↦ by rw [hzero k hk]; simp)] at he
  change (∑ k ∈ periodicCutoffBox n R, _ * _ * _) = g x
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : frequencyNorm k ≤ R
  · rw [periodicCutoffSymbol_eq_one hR hk]
    simp [g]
  · have hk' := hz k (lt_of_not_ge hk)
    change mFourierCoeff (fun x ↦ (f x : ℂ)) k = 0 at hk'
    simp [g, hk']

end JanetCartan
