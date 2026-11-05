module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Coordinates

/-!
# Ordered Euclidean coordinates for mixed carrier derivatives

The initial variables in `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse` consist of the scalar carrier coordinate,
the two remaining carrier coordinates, and all `n - 1` transverse coordinates.
This leaf flattens that exact list isometrically, to reuse the checked
Euclidean distributional derivative characterization. Its consumer is
`HasCarrierL2Derivatives`, not an η-moment condition.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CarrierSobolev
open ContinuumRow


/-- Scalar coordinate factor of `flatInitialEquiv`, for
`app:ch_background:prop:bg-adjoint`. -/
def initialScalarEuclideanEquiv : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  __ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm.toLinearEquiv
  norm_map' x := by simp [EuclideanSpace.norm_eq, PiLp.equivOfUnique, Real.sqrt_sq_eq_abs]

/-- Joining ordered coordinate blocks for `flatInitialEquiv`, for
`app:ch_background:prop:bg-adjoint`. -/
def initialEuclideanJoinEquiv (a b : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (a + b)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin a ⊕ Fin b => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

/-- Flatten the exact physical coordinate list for
`app:ch_background:prop:bg-adjoint`, preserving its Euclidean metric. -/
def flatInitialEquiv (n : ℕ) :
    InitialSpace n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (3 + (n - 1))) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    ((LinearIsometryEquiv.withLpProdCongr 2 initialScalarEuclideanEquiv
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))).trans (initialEuclideanJoinEquiv 1 2))
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin (n - 1))))).trans
      (initialEuclideanJoinEquiv 3 (n - 1))

/-- The first flattened coordinate is the scalar carrier coordinate in
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialEquiv_scalar (n : ℕ) (x : CarrierVariable n) :
    flatInitialEquiv n (initialCoordinates n x) (Fin.castAdd (n - 1) (Fin.castAdd 2 0)) = x.1.1 := by
  simp [flatInitialEquiv, initialEuclideanJoinEquiv, initialScalarEuclideanEquiv, initialCoordinates,
    LinearIsometryEquiv.piLpCongrLeft_apply, PiLp.equivOfUnique, MeasurableEquiv.prodCongr,
    WithLp.fst, WithLp.snd]
  rfl

/-- Both remaining carrier directions are retained in
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialEquiv_vector (n : ℕ) (x : CarrierVariable n) (i : Fin 2) :
    flatInitialEquiv n (initialCoordinates n x) (Fin.castAdd (n - 1) (Fin.natAdd 1 i)) = x.1.2 i := by
  simp [flatInitialEquiv, initialEuclideanJoinEquiv, initialScalarEuclideanEquiv, initialCoordinates,
    LinearIsometryEquiv.piLpCongrLeft_apply, PiLp.equivOfUnique, MeasurableEquiv.prodCongr,
    WithLp.fst, WithLp.snd]
  rw [finSumFinEquiv_symm_apply_natAdd (m := 1)]

/-- Every transverse coordinate is retained in
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialEquiv_transverse (n : ℕ) (x : CarrierVariable n) (i : Fin (n - 1)) :
    flatInitialEquiv n (initialCoordinates n x) (Fin.natAdd 3 i) = x.2 i := by
  simp [flatInitialEquiv, initialEuclideanJoinEquiv, initialScalarEuclideanEquiv, initialCoordinates,
    LinearIsometryEquiv.piLpCongrLeft_apply, PiLp.equivOfUnique, MeasurableEquiv.prodCongr,
    WithLp.fst, WithLp.snd]


/-- The full ordered coordinates on the literal product measure, for
`app:ch_background:prop:bg-adjoint`. -/
def flatInitialCoordinates (n : ℕ) :
    CarrierVariable n ≃ᵐ EuclideanSpace ℝ (Fin (3 + (n - 1))) :=
  (initialCoordinates n).trans (flatInitialEquiv n).toMeasurableEquiv


/-- The flattened coordinates preserve exactly `(ds dv) dy`, for
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (flatInitialCoordinates n) (carrierMeasure n) volume :=
  (flatInitialEquiv n).measurePreserving.comp (initialCoordinates_measurePreserving n)


/-- The reverse coordinates preserve Euclidean volume, for
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialCoordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (flatInitialCoordinates n).symm volume (carrierMeasure n) :=
  (flatInitialCoordinates_measurePreserving n).symm


/-- Flattening leaves the full initial frequency length unchanged, for
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialCoordinates_norm (n : ℕ) (x : CarrierVariable n) :
    ‖flatInitialCoordinates n x‖ = ‖initialCoordinates n x‖ :=
  (flatInitialEquiv n).norm_map _


/-- Literal carrier L² classes identified with ordered Euclidean L² classes,
for the mixed derivative family in `app:ch_background:prop:bg-adjoint`. -/
def flatInitialL2Equiv (n : ℕ) :
    CarrierL2 n ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (3 + (n - 1))))) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (flatInitialCoordinates n).symm
    (flatInitialCoordinates_symm_measurePreserving n)
  invFun := Lp.compMeasurePreserving (flatInitialCoordinates n)
    (flatInitialCoordinates_measurePreserving n)
  left_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using
      Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using
      Lp.compMeasurePreserving_id_apply f


/-- Representative of the actual coordinate change, for
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialL2Equiv_coeFn (n : ℕ) (f : CarrierL2 n) :
    flatInitialL2Equiv n f =ᵐ[volume] f ∘ (flatInitialCoordinates n).symm :=
  Lp.coeFn_compMeasurePreserving _ _


/-- Reverse representative of the actual coordinate change, for
`app:ch_background:prop:bg-adjoint`. -/
theorem flatInitialL2Equiv_symm_coeFn (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (3 + (n - 1)))))) :
    (flatInitialL2Equiv n).symm f =ᵐ[carrierMeasure n] f ∘ flatInitialCoordinates n :=
  Lp.coeFn_compMeasurePreserving _ _

end JanetCartan.CarrierSobolev
