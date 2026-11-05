module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeFlow

/-!
# Physical coordinate slices of the characteristic chart

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, use a
permutation of the Euclidean coordinates to select the time direction. This
constructs the covector duality needed by the physical operator; an arbitrary
linear equivalence would not identify its inverse with its transpose.

The consumer is `PhysicalOperator`: these exact slices hold the initial time
and covector fixed while differentiating the actual leading amplitude.
-/

open Set Matrix
open scoped InnerProductSpace ContDiff
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.RegularSector.Characteristic

variable {d : ℕ}

/-- Split off a chosen Euclidean coordinate as time; the remaining coordinates retain their
original order.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def coordinateSplit (i : Fin (d + 1)) : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x ↦ (x i, WithLp.toLp 2 fun j ↦ x (i.succAbove j))
    invFun := fun q ↦ WithLp.toLp 2 (i.insertNth q.1 (fun j ↦ q.2 j))
    left_inv := by
      intro x
      ext j
      exact congrFun (Fin.insertNth_self_removeNth i (fun k ↦ x k)) j
    right_inv := by
      intro q
      ext j <;> simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The time component is the selected original coordinate.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_fst (i : Fin (d + 1)) (x : Euclidean (d + 1)) :
    (coordinateSplit i x).1 = x i := rfl

/-- The spatial components are the remaining original coordinates.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_snd (i : Fin (d + 1)) (x : Euclidean (d + 1)) (j : Fin d) :
    (coordinateSplit i x).2 j = x (i.succAbove j) := rfl

/-- The inverse returns the specified time coordinate.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_symm_fst (i : Fin (d + 1)) (q : ℝ × Euclidean d) :
    (coordinateSplit i).symm q i = q.1 :=
  congrArg Prod.fst ((coordinateSplit i).apply_symm_apply q)

/-- The inverse returns each specified spatial coordinate.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_symm_snd (i : Fin (d + 1)) (q : ℝ × Euclidean d) (j : Fin d) :
    (coordinateSplit i).symm q (i.succAbove j) = q.2 j :=
  congrArg (fun p : ℝ × Euclidean d ↦ p.2 j) ((coordinateSplit i).apply_symm_apply q)

/-- The original time basis vector becomes the unit time direction.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_single_time (i : Fin (d + 1)) :
    coordinateSplit i (EuclideanSpace.single i 1) = (1, 0) := by
  ext j <;> simp [Fin.succAbove_ne]

/-- Each remaining basis vector becomes its spatial direction.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_single_space (i : Fin (d + 1)) (j : Fin d) :
    coordinateSplit i (EuclideanSpace.single (i.succAbove j) 1) =
      (0, EuclideanSpace.single j 1) := by
  ext k <;> simp [PiLp.single_apply, Fin.ne_succAbove]

/-- The inverse time direction is the original Euclidean basis vector.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_symm_time (i : Fin (d + 1)) :
    (coordinateSplit i).symm (1, 0) = EuclideanSpace.single i 1 := by
  apply (coordinateSplit i).injective
  simp

/-- The inverse spatial directions are the original Euclidean basis vectors.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem coordinateSplit_symm_space (i : Fin (d + 1)) (j : Fin d) :
    (coordinateSplit i).symm (0, EuclideanSpace.single j 1) =
      EuclideanSpace.single (i.succAbove j) 1 := by
  apply (coordinateSplit i).injective
  simp

/-- Insert fixed source time and initial covector into the physical variables.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def physicalSlice {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) : TwoTimePoint (Euclidean d) :=
  ((e x).1, (s, ((e x).2, η)))

/-- The exact differential of the physical slice, with both source parameters held fixed.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def physicalSliceDerivative {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)) :
    Euclidean n →L[ℝ] TwoTimePoint (Euclidean d) :=
  ((ContinuousLinearMap.fst ℝ ℝ (Euclidean d)).comp e.toContinuousLinearMap).prod
    ((0 : Euclidean n →L[ℝ] ℝ).prod
      (((ContinuousLinearMap.snd ℝ ℝ (Euclidean d)).comp e.toContinuousLinearMap).prod 0))

/-- The physical slice has its stated derivative.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem hasFDerivAt_physicalSlice {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) :
    HasFDerivAt (physicalSlice e s η) (physicalSliceDerivative e) x := by
  exact e.hasFDerivAt.fst.prodMk ((hasFDerivAt_const s x).prodMk
    (e.hasFDerivAt.snd.prodMk (hasFDerivAt_const η x)))

/-- The physical slice is smooth at every order.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem contDiff_physicalSlice {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (s : ℝ) (η : Euclidean d) : ContDiff ℝ ∞ (physicalSlice e s η) :=
  e.contDiff.fst.prodMk (contDiff_const.prodMk (e.contDiff.snd.prodMk contDiff_const))

/-- The slice differential changes only physical time and position.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem physicalSliceDerivative_apply {n : ℕ}
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d)) (v : Euclidean n) :
    physicalSliceDerivative e v = ((e v).1, (0, ((e v).2, 0))) := rfl

/-- The original physical point is unchanged by slicing.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem physicalSlice_position {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (s : ℝ) (η : Euclidean d) (x : Euclidean n) :
    e.symm ((physicalSlice e s η x).1, (physicalSlice e s η x).2.2.1) = x :=
  e.symm_apply_apply x

/-- Slicing at the chart point reconstructs all four variables exactly.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
@[simp] theorem physicalSlice_at {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (q : TwoTimePoint (Euclidean d)) :
    physicalSlice e q.2.1 q.2.2.2 (e.symm (q.1, q.2.2.1)) = q := by
  simp [physicalSlice]

/-- The constructed split preserves the covector pairing, with no metric or transpose assumption.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem coordinateSplit_covector_pairing (i : Fin (d + 1)) (ξ : ℝ × Euclidean d)
    (v : Euclidean (d + 1)) :
    ⟪(coordinateSplit i).symm ξ, v⟫_ℝ =
      ξ.1 * (coordinateSplit i v).1 + ⟪ξ.2, (coordinateSplit i v).2⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  rw [← Fin.add_sum_removeNth i]
  simp only [Fin.removeNth, coordinateSplit_fst, coordinateSplit_snd,
    coordinateSplit_symm_fst, coordinateSplit_symm_snd, mul_comm]

/-- A nonzero characteristic differential selects an actual coordinate time
with nonzero root derivative. The split and its covector duality are constructed,
not assumed (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_coordinateSplit_transverse
    (L : Euclidean (d + 1) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i : Fin (d + 1), L ((coordinateSplit i).symm (1, 0)) ≠ 0 := by
  by_contra! hz
  apply hL
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg L ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).sum_repr v)
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] at hv
  have hz' (i : Fin (d + 1)) : L (EuclideanSpace.single i 1) = 0 := by
    simpa only [coordinateSplit_symm_time] using hz i
  simpa only [hz', smul_zero, Finset.sum_const_zero, _root_.zero_apply] using hv.symm

end JanetCartan.RegularSector.Characteristic
