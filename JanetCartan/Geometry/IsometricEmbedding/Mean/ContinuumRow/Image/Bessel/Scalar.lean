module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Symbol

/-! # Scalar Bessel synthesis
The complete Fourier basis constructs the scalar multiplier needed for
`app:ch_background:defn:bg-row`. Evenness of its real symbol ensures reality.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

private theorem coeff_ae {f g : Torus n → ℂ} (h : f =ᵐ[volume] g) (k : Fin n → ℤ) :
    mFourierCoeff f k = mFourierCoeff g k := by
  simp only [mFourierCoeff_eq_volume_integral]
  exact integral_congr_ae (h.mono fun x hx ↦ by simp only [hx])

private theorem coeff_conj (f : Torus n → ℂ) (k : Fin n → ℤ) :
    mFourierCoeff (fun x ↦ conj (f x)) k = conj (mFourierCoeff f (-k)) := by
  simp only [mFourierCoeff, ← integral_conj, map_mul, ← mFourier_neg, neg_neg,
    smul_eq_mul]

/-- Scalar real L² synthesis of the Bessel symbol, used to construct the vector
operator of `app:ch_background:defn:bg-row`. -/
theorem exists_periodicBessel_scalar (u : PeriodicL2 n ℝ) :
    ∃ v : PeriodicL2 n ℝ, ∀ k,
      periodicFourierCoeff v k = periodicBesselSymbol k • periodicFourierCoeff u k := by
  let μ := Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hμ : (volume : Measure (Torus n)) = μ := torus_volume_eq_pi_haarAddCircle
  have hu : MemLp (fun x ↦ (u x : ℂ)) 2 μ := by
    rw [← hμ]
    exact (Lp.memLp u).ofReal
  let uc := hu.toLp (fun x ↦ (u x : ℂ))
  let a := mFourierBasis.repr uc
  let b : lp (fun _ : Fin n → ℤ ↦ ℂ) 2 := ⟨fun k ↦ periodicBesselSymbol k • a k,
    (lp.memℓp a).mono' (fun k ↦ by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
      exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k))⟩
  let z := mFourierBasis.repr.symm b
  have hz (k : Fin n → ℤ) :
      mFourierCoeff z k = (periodicBesselSymbol k : ℂ) *
        mFourierCoeff (fun x ↦ (u x : ℂ)) k := by
    rw [← mFourierBasis_repr]
    change mFourierBasis.repr (mFourierBasis.repr.symm b) k = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    change periodicBesselSymbol k • mFourierBasis.repr uc k = _
    rw [mFourierBasis_repr]
    have he : (uc : Torus n → ℂ) =ᵐ[volume] fun x ↦ (u x : ℂ) := by
      simpa only [hμ] using hu.coeFn_toLp
    rw [coeff_ae he]
    rfl
  have hc (k : Fin n → ℤ) :
      mFourierCoeff (fun x ↦ (u x : ℂ)) (-k) =
        conj (mFourierCoeff (fun x ↦ (u x : ℂ)) k) := by
    simpa using (coeff_conj (fun x ↦ (u x : ℂ)) (-k))
  let zc := Complex.conjCLE.toContinuousLinearMap.compLp z
  have hzc : zc = z := by
    apply mFourierBasis.repr.injective
    apply lp.ext
    funext k
    rw [mFourierBasis_repr, mFourierBasis_repr]
    have he : (zc : Torus n → ℂ) =ᵐ[volume] fun x ↦ conj (z x) := by
      rw [hμ]; exact Complex.conjCLE.toContinuousLinearMap.coeFn_compLp z
    rw [coeff_ae he, coeff_conj, hz, hz, periodicBesselSymbol_neg, hc]
    simp
  have hreal : (fun x ↦ ((z x).re : ℂ)) =ᵐ[volume] z := by
    have he := Complex.conjCLE.toContinuousLinearMap.coeFn_compLp z
    change (zc : Torus n → ℂ) =ᵐ[μ] _ at he
    rw [hzc, ← hμ] at he
    filter_upwards [he] with x hx
    change z x = conj (z x) at hx
    apply Complex.ext
    · rfl
    · have hi := congrArg Complex.im hx
      simp only [Complex.conj_im] at hi
      simp only [Complex.ofReal_im]
      linarith
  have hzLp : MemLp (fun x ↦ (z x).re) 2 volume := by
    rw [hμ]
    exact (Lp.memLp z).continuousLinearMap_comp Complex.reCLM
  let v := hzLp.toLp (fun x ↦ (z x).re)
  refine ⟨v, fun k ↦ ?_⟩
  have hv : (fun x ↦ (v x : ℂ)) =ᵐ[volume] z := by
    filter_upwards [hzLp.coeFn_toLp, hreal] with x hx hx'
    exact (congrArg Complex.ofReal hx).trans hx' 
  have h := hz k
  rw [← coeff_ae hv, mFourierCoeff_ofReal_memLp (Lp.memLp v),
    mFourierCoeff_ofReal_memLp (Lp.memLp u)] at h
  apply Prod.ext
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

end JanetCartan.ContinuumRow
