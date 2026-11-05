module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Iterated
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Value maps on the actual periodic Sobolev spaces

The coordinate projections, real inclusion, and real part needed to transfer
`DifferentialChart.torusSobolevCommutator` to the continuum normal in
`app:ch_background:eq:bg-commutator` act on the existing Fourier Sobolev spaces.
Their norms are controlled by the same value maps, with unchanged torus measure.
The weak derivative compatibility uses the actual adjoint on test values.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator

open PeriodicSobolevSpace

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Value maps commute with Fourier coefficients of actual L² classes. This
supplies the coordinate and real-inclusion Sobolev maps for
`app:ch_background:eq:bg-commutator`. -/
theorem fourierCoeff_compLpL (L : F →L[ℝ] G) (u : PeriodicL2 n F)
    (k : Fin n → ℤ) :
    periodicFourierCoeff (L.compLpL 2 volume u) k =
      (L (periodicFourierCoeff u k).1, L (periodicFourierCoeff u k).2) := by
  rw [periodicFourierCoeff_congr_ae (L.coeFn_compLpL u)]
  apply Prod.ext
  · change (∫ x : Torus n, _ • L (u x)) = L (∫ x : Torus n, _ • u x)
    simp_rw [← L.map_smul]
    apply L.integral_comp_comm
    exact ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  · change (∫ x : Torus n, _ • L (u x)) = L (∫ x : Torus n, _ • u x)
    simp_rw [← L.map_smul]
    apply L.integral_comp_comm
    exact ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)

private theorem norm_fourierCoeff_compLpL_le (L : F →L[ℝ] G)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    ‖periodicL2FourierCoeff k (L.compLpL 2 volume u)‖ ≤
      ‖L‖ * ‖periodicL2FourierCoeff k u‖ := by
  have hr := L.le_opNorm (periodicFourierCoeff u k).1
  have hi := L.le_opNorm (periodicFourierCoeff u k).2
  have hr' := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hr
  have hi' := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hi
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp only [periodicL2FourierCoeff_apply, WithLp.prod_norm_sq_eq_of_L2,
    fourierCoeff_compLpL, mul_pow]
  change ‖L (periodicFourierCoeff u k).1‖ ^ 2 +
    ‖L (periodicFourierCoeff u k).2‖ ^ 2 ≤
    ‖L‖ ^ 2 * (‖(periodicFourierCoeff u k).1‖ ^ 2 +
      ‖(periodicFourierCoeff u k).2‖ ^ 2)
  nlinarith

private theorem norm_weighted_compLpL_le (L : F →L[ℝ] G) (s : ℕ)
    (u : PeriodicL2 n F) (k : Fin n → ℤ) :
    ‖weightedPeriodicL2FourierCoeff s (L.compLpL 2 volume u) k‖ ≤
      ‖‖L‖ • weightedPeriodicL2FourierCoeff s u k‖ := by
  simp only [weightedPeriodicL2FourierCoeff_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg L)]
  have h := mul_le_mul_of_nonneg_left (norm_fourierCoeff_compLpL_le L u k)
    (abs_nonneg (periodicSobolevWeight s k))
  nlinarith

/-- Pointwise value maps preserve the actual Fourier Sobolev level. The
producer is the coefficient calculation, not an assumed regularity estimate
(`app:ch_background:eq:bg-commutator`). -/
theorem compLpL_mem (L : F →L[ℝ] G) (s : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F s) :
    L.compLpL 2 volume u ∈ periodicSobolevLevel n G s :=
  Memℓp.mono' (hu.const_smul ‖L‖) (norm_weighted_compLpL_le L s u)

/-- Algebraic value map on the actual Sobolev level, used to construct
`sobolevMap` (`app:ch_background:eq:bg-commutator`). -/
def sobolevMapLinear (L : F →L[ℝ] G) (s : ℕ) :
    PeriodicSobolevSpace n F s →ₗ[ℝ] PeriodicSobolevSpace n G s where
  toFun u := ofL2 s (L.compLpL 2 volume (toL2 s u))
    (compLpL_mem L s (toL2 s u) (toL2_mem s u))
  map_add' u v := by
    apply toL2_injective s
    simp only [map_add, toL2_ofL2]
  map_smul' c u := by
    apply toL2_injective s
    simp only [map_smul, toL2_ofL2, RingHom.id_apply]

/-- Bound for the algebraic value map used in `sobolevMap`
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_sobolevMapLinear_le (L : F →L[ℝ] G) (s : ℕ)
    (u : PeriodicSobolevSpace n F s) :
    ‖sobolevMapLinear L s u‖ ≤ ‖L‖ * ‖u‖ := by
  change ‖analysis s (sobolevMapLinear L s u)‖ ≤ ‖L‖ * ‖analysis s u‖
  rw [← norm_smul_of_nonneg (norm_nonneg L)]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  exact norm_weighted_compLpL_le L s (toL2 s u)

/-- The continuous Sobolev value map used for real inclusion and coordinate
extraction in the continuum commutator (`app:ch_background:eq:bg-commutator`). -/
def sobolevMap (L : F →L[ℝ] G) (s : ℕ) :
    PeriodicSobolevSpace n F s →L[ℝ] PeriodicSobolevSpace n G s :=
  (sobolevMapLinear L s).mkContinuous ‖L‖ (norm_sobolevMapLinear_le L s)

/-- The Sobolev map has the original pointwise L² value map as its realization
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_sobolevMap (L : F →L[ℝ] G) (s : ℕ)
    (u : PeriodicSobolevSpace n F s) :
    toL2 s (sobolevMap L s u) = L.compLpL 2 volume (toL2 s u) := rfl

/-- Value-map bounds incur no change of Sobolev norm or measure
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_sobolevMap_le (L : F →L[ℝ] G) (s : ℕ)
    (u : PeriodicSobolevSpace n F s) : ‖sobolevMap L s u‖ ≤ ‖L‖ * ‖u‖ :=
  norm_sobolevMapLinear_le L s u

/-- Real inclusion and coordinate extraction agree with their literal smooth
representatives (`app:ch_background:eq:bg-commutator`). -/
theorem sobolevMap_ofSmooth (L : F →L[ℝ] G) (s : ℕ)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    sobolevMap L s (ofSmooth s f hf) =
      ofSmooth s (fun x ↦ L (f x)) (hf.comp_clm L) := by
  apply toL2_injective s
  rw [toL2_sobolevMap]
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (toL2 s (ofSmooth s f hf)),
    toL2_ofSmooth_ae s f hf,
    toL2_ofSmooth_ae s (fun x ↦ L (f x)) (hf.comp_clm L)] with x hx hy hz
  rw [hx, hy, hz]

/-- The literal L² value map on a smooth field, allowing a change of its
Sobolev realization order (`app:ch_background:eq:bg-commutator`). -/
theorem compLpL_ofSmooth (L : F →L[ℝ] G) (s t : ℕ)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    L.compLpL 2 volume (toL2 s (ofSmooth s f hf)) =
      toL2 t (ofSmooth t (fun x ↦ L (f x)) (hf.comp_clm L)) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (toL2 s (ofSmooth s f hf)),
    toL2_ofSmooth_ae s f hf,
    toL2_ofSmooth_ae t (fun x ↦ L (f x)) (hf.comp_clm L)] with x hx hy hz
  rw [hx, hy, hz]

/-- Value maps commute with the L² realization of a smooth ordered derivative.
This is the top-derivative compatibility for real compression
(`app:ch_background:eq:bg-commutator`). -/
theorem compLpL_derivative_ofSmooth (L : F →L[ℝ] G) (s t : ℕ)
    (is : List (Fin n)) (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    L.compLpL 2 volume (toL2 s (ofSmooth s (periodicCoordinateDerivList is f)
      (hf.coordinateDerivList is))) =
      toL2 t (ofSmooth t (periodicCoordinateDerivList is (fun x ↦ L (f x)))
        ((hf.comp_clm L).coordinateDerivList is)) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (toL2 s (ofSmooth s
      (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))),
    toL2_ofSmooth_ae s _ (hf.coordinateDerivList is),
    toL2_ofSmooth_ae t _ ((hf.comp_clm L).coordinateDerivList is)] with x hx hy hz
  rw [hx, hy, hz, periodicCoordinateDerivList_comp_clm hf L]

/-- Constant value maps commute with the independently defined distributional
derivative. The real compression of the matrix commutator uses this with
`euclideanRealPart` (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_compLpL (L : F →L[ℝ] G) (is : List (Fin n))
    {u v : PeriodicL2 n F} (h : HasPeriodicWeakDerivativeList is u v) :
    HasPeriodicWeakDerivativeList is (L.compLpL 2 volume u) (L.compLpL 2 volume v) := by
  intro φ hφ
  have he (w : PeriodicL2 n F) (ψ : Torus n → G) :
      (∫ x, ⟪(L.compLpL 2 volume w) x, ψ x⟫) =
        ∫ x, ⟪w x, L.adjoint (ψ x)⟫ := by
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLpL w] with x hx
    rw [hx, ContinuousLinearMap.adjoint_inner_right]
  rw [he, h _ (hφ.comp_clm L.adjoint), he,
    periodicCoordinateDerivList_comp_clm hφ L.adjoint]

/-- Inner-product form of the actual ordered weak derivative, for combining
matrix entries and weighted normal summands (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_iff_inner (is : List (Fin n)) (u v : PeriodicL2 n F) :
    HasPeriodicWeakDerivativeList is u v ↔ ∀ (φ : Torus n → F)
      (hφ : IsSmoothPeriodic φ),
      ⟪v, toL2 0 (ofSmooth 0 φ hφ)⟫ = (-1 : ℝ) ^ is.length *
        ⟪u, toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse φ)
          (hφ.coordinateDerivList is.reverse))⟫ := by
  simp only [inner_periodicL2_ofSmooth]
  rfl

/-- Addition of actual distributional derivatives, for the matrix/exterior
assembly (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_add {is : List (Fin n)} {u v u' v' : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivativeList is u v)
    (h' : HasPeriodicWeakDerivativeList is u' v') :
    HasPeriodicWeakDerivativeList is (u + u') (v + v') := by
  rw [weakDerivativeList_iff_inner] at h h' ⊢
  intro φ hφ
  simp only [inner_add_left, h φ hφ, h' φ hφ, mul_add]

/-- Real weights commute with the actual weak derivative, preserving in
particular the carrier factor four (`app:ch_background:eq:bg-realification`). -/
theorem weakDerivativeList_smul {is : List (Fin n)} {u v : PeriodicL2 n F}
    (h : HasPeriodicWeakDerivativeList is u v) (c : ℝ) :
    HasPeriodicWeakDerivativeList is (c • u) (c • v) := by
  rw [weakDerivativeList_iff_inner] at h ⊢
  intro φ hφ
  simp only [real_inner_smul_left, h φ hφ]
  ring

/-- Finite sums preserve the weak derivative identity for the full represented
normal (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_sum {κ : Type*} (t : Finset κ)
    (is : List (Fin n)) (u v : κ → PeriodicL2 n F)
    (h : ∀ a ∈ t, HasPeriodicWeakDerivativeList is (u a) (v a)) :
    HasPeriodicWeakDerivativeList is (∑ a ∈ t, u a) (∑ a ∈ t, v a) := by
  rw [weakDerivativeList_iff_inner]
  intro φ hφ
  simp only [sum_inner, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a ha ↦
    (weakDerivativeList_iff_inner is (u a) (v a)).mp (h a ha) φ hφ)

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
