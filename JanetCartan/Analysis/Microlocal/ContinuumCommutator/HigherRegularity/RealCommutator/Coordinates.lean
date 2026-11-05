module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Postcomposition
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Coordinates

/-!
# Coordinates of the actual periodic Sobolev space

The shared finite L² coordinate isometry is compatible with the Sobolev
realization and the ordered distributional derivatives used in
`app:ch_background:eq:bg-commutator`. This is the input/output interface for
transferring the scalar full-amplitude commutators to the vector continuum normal.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
open JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
open PeriodicSobolevSpace
variable {n : ℕ} {I : Type*} [Fintype I]

/-- A complex coordinate regarded as a real-linear value map. It is the value
map underlying the shared L² isometry (`app:ch_background:eq:bg-commutator`). -/
def valueCoordinate (i : I) : EuclideanSpace ℂ I →L[ℝ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i).restrictScalars ℝ

/-- Coordinate extraction is contractive (`app:ch_background:eq:bg-commutator`). -/
theorem norm_valueCoordinate_le (i : I) : ‖valueCoordinate i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

/-- The shared coordinate isometry is the literal L² value map; the measure is
unchanged (`app:ch_background:eq:bg-commutator`). -/
theorem coordinateIsometry_apply (u : PeriodicL2 n (EuclideanSpace ℂ I)) (i : I) :
    finiteL2CoordinateIsometry volume u i = (valueCoordinate i).compLpL 2 volume u := by
  apply Lp.ext
  exact (finiteL2Coordinates_apply_ae volume u i).trans
    ((valueCoordinate i).coeFn_compLpL u).symm

/-- Coordinates on the actual vector Sobolev space, with the Hilbert norm on
the row family (`app:ch_background:eq:bg-commutator`). -/
def sobolevCoordinates (s : ℕ) : PeriodicSobolevSpace n (EuclideanSpace ℂ I) s →L[ℝ]
    PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace n ℂ s) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ sobolevMap (valueCoordinate i) s)

/-- Row formula for Sobolev coordinates (`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem sobolevCoordinates_apply (s : ℕ)
    (u : PeriodicSobolevSpace n (EuclideanSpace ℂ I) s) (i : I) :
    sobolevCoordinates s u i = sobolevMap (valueCoordinate i) s u := rfl

/-- The Sobolev coordinate map realizes exactly the existing L² coordinate
isometry (`app:ch_background:eq:bg-commutator`). -/
theorem toL2_sobolevCoordinates (s : ℕ)
    (u : PeriodicSobolevSpace n (EuclideanSpace ℂ I) s) :
    WithLp.toLp 2 (fun i ↦ toL2 s (sobolevCoordinates s u i)) =
      finiteL2CoordinateIsometry volume (toL2 s u) := by
  apply PiLp.ext
  intro i
  exact (coordinateIsometry_apply (toL2 s u) i).symm

/-- Each coordinate has no larger Sobolev norm. This feeds the entrywise
additive commutator estimate (`app:ch_background:eq:bg-commutator`). -/
theorem norm_sobolevCoordinates_apply_le (s : ℕ)
    (u : PeriodicSobolevSpace n (EuclideanSpace ℂ I) s) (i : I) :
    ‖sobolevCoordinates s u i‖ ≤ ‖u‖ := by
  apply (norm_sobolevMap_le (valueCoordinate i) s u).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_valueCoordinate_le i) (norm_nonneg u)

/-- A fixed dimension bound for Sobolev row extraction. No coefficient budget
enters this bound (`app:ch_background:eq:bg-commutator`). -/
theorem norm_sobolevCoordinates_le (s : ℕ)
    (u : PeriodicSobolevSpace n (EuclideanSpace ℂ I) s) :
    ‖sobolevCoordinates s u‖ ≤ (Fintype.card I : ℝ) * ‖u‖ := by
  classical
  have he : sobolevCoordinates s u =
      ∑ i : I, PiLp.single 2 i (sobolevCoordinates s u i) := by
    ext i
    simp [Pi.single_apply]
  calc
    _ ≤ ∑ i : I, ‖sobolevCoordinates s u i‖ := by
      conv_lhs => rw [he]
      simpa only [PiLp.norm_single] using
        norm_sum_le Finset.univ (fun i ↦
          (PiLp.single 2 i (sobolevCoordinates s u i) :
            PiLp 2 (fun _ : I ↦ PeriodicSobolevSpace n ℂ s)))
    _ ≤ ∑ _i : I, ‖u‖ := Finset.sum_le_sum fun i _ ↦
      norm_sobolevCoordinates_apply_le s u i
    _ = _ := by simp

/-- Smooth coordinate representatives agree at every Sobolev order
(`app:ch_background:eq:bg-commutator`). -/
theorem sobolevCoordinates_ofSmooth (s : ℕ) (f : Torus n → EuclideanSpace ℂ I)
    (hf : IsSmoothPeriodic f) (i : I) :
    sobolevCoordinates s (ofSmooth s f hf) i =
      ofSmooth s (fun x ↦ f x i) (hf.comp_clm (valueCoordinate i)) :=
  sobolevMap_ofSmooth (valueCoordinate i) s f hf

/-- Literal smooth formula for the shared L² coordinate isometry
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateIsometry_ofSmooth (s t : ℕ) (f : Torus n → EuclideanSpace ℂ I)
    (hf : IsSmoothPeriodic f) (i : I) :
    finiteL2CoordinateIsometry volume (toL2 s (ofSmooth s f hf)) i =
      toL2 t (ofSmooth t (fun x ↦ f x i) (hf.comp_clm (valueCoordinate i))) := by
  rw [coordinateIsometry_apply]
  exact compLpL_ofSmooth (valueCoordinate i) s t f hf

/-- The real L² pairing is the sum of the coordinate pairings through the
shared isometry (`app:ch_background:eq:bg-commutator`). -/
theorem inner_eq_sum_coordinates (u v : PeriodicL2 n (EuclideanSpace ℂ I)) :
    ⟪u, v⟫ = ∑ i, ⟪finiteL2CoordinateIsometry volume u i,
      finiteL2CoordinateIsometry volume v i⟫ := by
  rw [← PiLp.inner_apply]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, LinearIsometryEquiv.norm_map]

/-- Ordered weak derivatives of the actual vector L² field are equivalent to
ordered weak derivatives of all its scalar rows. This closes the distributional
part of the scalar-to-vector transfer (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_coordinates_iff (is : List (Fin n))
    (u v : PeriodicL2 n (EuclideanSpace ℂ I)) :
    HasPeriodicWeakDerivativeList is u v ↔ ∀ i,
      HasPeriodicWeakDerivativeList is (finiteL2CoordinateIsometry volume u i)
        (finiteL2CoordinateIsometry volume v i) := by
  constructor
  · intro h i
    simp only [coordinateIsometry_apply]
    exact weakDerivativeList_compLpL (valueCoordinate i) is h
  · intro h
    rw [weakDerivativeList_iff_inner]
    intro φ hφ
    simp only [inner_eq_sum_coordinates, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi := (weakDerivativeList_iff_inner is _ _).mp (h i)
      (fun x ↦ φ x i) (hφ.comp_clm (valueCoordinate i))
    have hd : periodicCoordinateDerivList is.reverse (fun x ↦ φ x i) =
        fun x ↦ periodicCoordinateDerivList is.reverse φ x i :=
      periodicCoordinateDerivList_comp_clm hφ (valueCoordinate i) is.reverse
    simpa only [coordinateIsometry_ofSmooth 0 0, hd] using hi

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
