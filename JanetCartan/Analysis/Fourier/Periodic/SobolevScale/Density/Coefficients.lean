module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Complete
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Scalar

/-!
# Fourier cutoff coefficients for square-integrable fields

The finite Fourier approximations used for smooth density in
`app:not:fourier` and `app:ch_background:prop:bg-inverse` apply to actual L²
representatives, without any continuity assumption on the input.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate RealInnerProductSpace

namespace JanetCartan

variable {n : ℕ}

/-- Complex encoding of a square-integrable real coefficient pair
(`app:not:fourier`). -/
theorem mFourierCoeff_ofReal_memLp {f : Torus n → ℝ} (hf : MemLp f 2)
    (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ (f x : ℂ)) k =
      ⟨(periodicFourierCoeff f k).1, (periodicFourierCoeff f k).2⟩ := by
  have hi : Integrable (fun x ↦ mFourier (-k) x * (f x : ℂ)) :=
    (hf.ofReal (K := ℂ)).integrable (by norm_num) |>.bdd_mul
      (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (mFourier (-k)).norm_coe_le_norm x))
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
theorem ofReal_periodicCutoff_memLp {f : Torus n → ℝ} (hf : MemLp f 2) (R : ℝ) (x : Torus n) :
    Complex.ofReal (periodicCutoff R f x) = ∑ k ∈ periodicCutoffBox n R,
      (periodicCutoffSymbol R k : ℂ) *
        mFourierCoeff (fun y ↦ (f y : ℂ)) k * mFourier k x := by
  have hc := conjugate_sum (periodicCutoffBox n R) (neg_mem_periodicCutoffBox R)
    (fun k ↦ (periodicCutoffSymbol R k : ℂ) * mFourierCoeff (fun y ↦ (f y : ℂ)) k)
    (by intro k; simp [periodicCutoffSymbol_neg, coeff_conj_ofReal]) x
  apply Complex.ext
  · simp [periodicCutoff, periodicFourierMode, mFourierCoeff_ofReal_memLp hf,
      Complex.mul_re, Complex.mul_im, mul_sub, mul_assoc, mul_comm]
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

/-- The scalar multiplier has exactly the prescribed Fourier coefficients
(`main:lem:smoothing`). -/
theorem mFourierCoeff_periodicCutoff_memLp {f : Torus n → ℝ} (hf : MemLp f 2)
    {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ Complex.ofReal (periodicCutoff R f x)) k =
      (periodicCutoffSymbol R k : ℂ) * mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  simp_rw [ofReal_periodicCutoff_memLp hf]
  rw [mFourierCoeff_finset_sum]
  split_ifs with hk
  · rfl
  · rw [periodicCutoffSymbol_eq_zero_of_notMem hR hk, Complex.ofReal_zero, zero_mul]

/-- The coefficient identity in the shared real-pair notation (`main:lem:smoothing`). -/
theorem periodicFourierCoeff_periodicCutoff_scalar_memLp {f : Torus n → ℝ} (hf : MemLp f 2)
    {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCutoff R f) k =
      periodicCutoffSymbol R k • periodicFourierCoeff f k := by
  have h := mFourierCoeff_periodicCutoff_memLp hf hR k
  rw [mFourierCoeff_ofReal (isSmoothPeriodic_periodicCutoff R f).1,
    mFourierCoeff_ofReal_memLp hf] at h
  apply Prod.ext
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Taking a real scalar coordinate commutes with the finite cutoff even for
L² inputs (`app:not:fourier`). -/
theorem periodicCutoff_inner_memLp {f : Torus n → F} (hf : MemLp f 2)
    (v : F) (R : ℝ) :
    periodicCutoff R (fun x ↦ ⟪v, f x⟫) = fun x ↦ ⟪v, periodicCutoff R f x⟫ := by
  funext x
  simp [periodicCutoff, periodicFourierMode, periodicFourierCoeff_inner hf,
    inner_sum, inner_sub_right, inner_smul_right]

/-- Exact multiplier identity on arbitrary square-integrable real fields
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicFourierCoeff_periodicCutoff_memLp {f : Torus n → F}
    (hf : MemLp f 2) {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCutoff R f) k =
      periodicCutoffSymbol R k • periodicFourierCoeff f k := by
  have hout : MemLp (periodicCutoff R f) 2 :=
    (isSmoothPeriodic_periodicCutoff R f).1.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h (v : F) :
      periodicFourierCoeff (periodicCutoff R (fun x ↦ ⟪v, f x⟫)) k =
        periodicCutoffSymbol R k • periodicFourierCoeff (fun x ↦ ⟪v, f x⟫) k :=
    periodicFourierCoeff_periodicCutoff_scalar_memLp
      (hf.continuousLinearMap_comp (innerSL ℝ v)) hR k
  simp only [periodicCutoff_inner_memLp hf, periodicFourierCoeff_inner hout,
    periodicFourierCoeff_inner hf] at h
  apply Prod.ext
  · apply ext_inner_left ℝ
    intro v
    simpa only [Prod.smul_fst, inner_smul_right, smul_eq_mul] using congrArg Prod.fst (h v)
  · apply ext_inner_left ℝ
    intro v
    simpa only [Prod.smul_snd, inner_smul_right, smul_eq_mul] using congrArg Prod.snd (h v)

end JanetCartan
