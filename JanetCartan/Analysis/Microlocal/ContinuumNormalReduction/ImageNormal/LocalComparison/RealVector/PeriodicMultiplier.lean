module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel.Operator

/-!
# Complex scalar realization of the periodic image inverse

The scalar multiplier used by the local comparison in
`app:ch_background:prop:bg-frame`, Step 1, is constructed from the complete
Fourier basis. Its symbol is the one of the actual real inverse in
`app:ch_background:defn:bg-row`.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {n : ℕ}

private def besselSequence (a : lp (fun _ : Fin n → ℤ ↦ ℂ) 2) :
    lp (fun _ : Fin n → ℤ ↦ ℂ) 2 :=
  ⟨fun k ↦ periodicBesselSymbol k • a k,
    (lp.memℓp a).mono' (fun k ↦ by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
      exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k))⟩

private def besselSequenceOperator : lp (fun _ : Fin n → ℤ ↦ ℂ) 2 →L[ℂ]
    lp (fun _ : Fin n → ℤ ↦ ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := besselSequence
      map_add' := fun a b ↦ by
        apply lp.ext
        funext k
        exact smul_add _ _ _
      map_smul' := fun c a ↦ by
        apply lp.ext
        funext k
        change periodicBesselSymbol k • (c • a k) = c • (periodicBesselSymbol k • a k)
        exact smul_comm _ _ _ }
    1 (fun a ↦ by
      simpa only [one_mul] using
        (lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
          (fun k ↦ by
            change ‖periodicBesselSymbol k • a k‖ ≤ ‖a k‖
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
            exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k))))

/-- Fourier synthesis constructs a complex scalar contraction with the image
symbol (`app:ch_background:defn:bg-row`); used to define the bounded multiplier. -/
theorem exists_complexPeriodicBesselOperator :
    ∃ J : PeriodicL2 n ℂ →L[ℂ] PeriodicL2 n ℂ,
      (∀ u k, mFourierCoeff (J u) k =
        (periodicBesselSymbol k : ℂ) * mFourierCoeff u k) ∧
      ∀ u, ‖J u‖ ≤ ‖u‖ := by
  unfold PeriodicL2
  rw [torus_volume_eq_pi_haarAddCircle]
  let e := (mFourierBasis (d := Fin n)).repr
  refine ⟨e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (besselSequenceOperator.comp e.toContinuousLinearEquiv.toContinuousLinearMap), ?_, ?_⟩
  · intro u k
    change mFourierCoeff (e.symm (besselSequenceOperator (e u))) k = _
    rw [← mFourierBasis_repr]
    change e (e.symm (besselSequenceOperator (e u))) k = _
    rw [e.apply_symm_apply]
    change periodicBesselSymbol k • e u k = _
    rw [show e u k = mFourierCoeff u k from mFourierBasis_repr u k]
    rfl
  · intro u
    change ‖e.symm (besselSequenceOperator (e u))‖ ≤ ‖u‖
    rw [e.symm.norm_map, ← e.norm_map u]
    apply lp.norm_mono (by norm_num)
    intro k
    change ‖periodicBesselSymbol k • e u k‖ ≤ ‖e u k‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (periodicBesselSymbol_pos k)]
    exact mul_le_of_le_one_left (norm_nonneg _) (periodicBesselSymbol_le_one k)

/-- The bounded complex scalar periodic Bessel inverse for the coordinate
comparison in `app:ch_background:prop:bg-frame`, Step 1. -/
def complexPeriodicBesselOperator : PeriodicL2 n ℂ →L[ℂ] PeriodicL2 n ℂ :=
  (exists_complexPeriodicBesselOperator (n := n)).choose

/-- Literal complex Fourier action, constructed without a Fourier bridge
hypothesis (`app:ch_background:defn:bg-row`). -/
theorem mFourierCoeff_complexPeriodicBesselOperator (u : PeriodicL2 n ℂ)
    (k : Fin n → ℤ) :
    mFourierCoeff (complexPeriodicBesselOperator u) k =
      (periodicBesselSymbol k : ℂ) * mFourierCoeff u k :=
  exists_complexPeriodicBesselOperator.choose_spec.1 u k

/-- The scalar image inverse is a contraction (`app:ch_background:defn:bg-row`). -/
theorem norm_complexPeriodicBesselOperator_apply_le (u : PeriodicL2 n ℂ) :
    ‖complexPeriodicBesselOperator u‖ ≤ ‖u‖ :=
  exists_complexPeriodicBesselOperator.choose_spec.2 u

/-- Fourier uniqueness used to compare real coordinates with the scalar image
inverse (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexPeriodicL2_eq_of_mFourierCoeff_eq {u v : PeriodicL2 n ℂ}
    (h : ∀ k, mFourierCoeff u k = mFourierCoeff v k) : u = v := by
  revert u v
  unfold PeriodicL2
  rw [torus_volume_eq_pi_haarAddCircle]
  intro u v h
  apply (mFourierBasis (d := Fin n)).repr.injective
  apply lp.ext
  funext k
  simpa only [mFourierBasis_repr] using h k

end JanetCartan.ContinuumNormalReduction.ImageNormal
