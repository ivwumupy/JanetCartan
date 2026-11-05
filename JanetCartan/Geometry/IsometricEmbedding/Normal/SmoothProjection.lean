module

public import JanetCartan.Geometry.IsometricEmbedding.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Projection
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Smooth normal projection of an immersion

For Section 2 (`main:sec:geometry`) and Definition `app:ch_waves:defn:geometry`,
the actual orthogonal normal projection is the smooth matrix
`I - dF γ(F)⁻¹ (dF)ᵀ` on the open immersion domain. Positive definiteness of the
induced metric supplies invertibility, a local determinant gap, and a uniform
gap on compact subsets. Smooth inversion therefore requires no extra premise.

The explicit projected Hessian is identified with `secondFundamentalForm`.
The finite-regularity statements lose one derivative for the projection and two
for the second form; they also apply with all orders equal to ∞. Matrices use
the Frobenius norm throughout.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open Set

namespace JanetCartan

variable {n N : ℕ} {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
  {r m : ℕ∞ω}


/-! ## The immersion domain and determinant gaps -/

/-- Section 2 (`main:sec:geometry`): the points of a coordinate domain where `dF` is injective. -/
def immersionDomain (F : Euclidean n → Euclidean N) (s : Set (Euclidean n)) :
    Set (Euclidean n) := {x | x ∈ s ∧ Function.Injective (fderiv ℝ F x)}

/-- Section 2 (`main:sec:geometry`): the immersion domain of a C¹ map is open. -/
theorem isOpen_immersionDomain (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s) :
    IsOpen (immersionDomain F s) := by
  exact ((hF.fderiv_of_isOpen hs (m := 0) (by simp)).continuousOn).isOpen_inter_preimage
    hs ContinuousLinearMap.isOpen_injective

/-- Section 2 (`main:sec:geometry`): restriction to the immersion domain is an immersion. -/
theorem isImmersionOn_immersionDomain (F : Euclidean n → Euclidean N)
    (s : Set (Euclidean n)) : IsImmersionOn F (immersionDomain F s) :=
  fun _ hx ↦ hx.2

/-- Section 2 (`main:sec:geometry`): the Gram determinant is positive at every immersion point. -/
theorem inducedMetric_det_pos {x : Euclidean n}
    (himm : Function.Injective (fderiv ℝ F x)) : 0 < (inducedMetric F x).det :=
  (inducedMetric_posDef himm).det_pos

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the determinant stays bounded away
from zero on a neighborhood of an immersion point of a C¹ map. -/
theorem exists_inducedMetric_det_local_lowerBound (hs : IsOpen s)
    (hF : ContDiffOn ℝ 1 F s) {x : Euclidean n} (hx : x ∈ s)
    (himm : Function.Injective (fderiv ℝ F x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set (Euclidean n),
      IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧ ∀ y ∈ U, δ ≤ (inducedMetric F y).det := by
  let δ := (inducedMetric F x).det / 2
  have hpos := inducedMetric_det_pos himm
  have hc : ContinuousOn (fun y ↦ (inducedMetric F y).det) s :=
    continuous_id.matrix_det.comp_continuousOn (continuousOn_inducedMetric hs hF)
  refine ⟨δ, half_pos hpos, s ∩ (fun y ↦ (inducedMetric F y).det) ⁻¹' Ioi δ,
    hc.isOpen_inter_preimage hs isOpen_Ioi, ⟨hx, ?_⟩, inter_subset_left, ?_⟩
  · exact half_lt_self hpos
  · intro y hy
    exact le_of_lt hy.2

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: a uniform positive determinant gap
on every compact subset of a C¹ immersion domain. -/
theorem exists_inducedMetric_det_lowerBound (hs : IsOpen s) (hF : ContDiffOn ℝ 1 F s)
    (himm : IsImmersionOn F s) {K : Set (Euclidean n)} (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ (inducedMetric F x).det := by
  exact hK.exists_forall_le'
    ((continuous_id.matrix_det).comp_continuousOn
      ((continuousOn_inducedMetric hs hF).mono hKs))
    (fun x hx ↦ inducedMetric_det_pos (himm x (hKs hx)))

/-! ## Inverse metric and operator-valued projections -/

-- Transfer between coordinate and Frobenius matrix norms.
private def matrixEntry (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  let L : MetricTensor n →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: inverse-metric composition preserves
the regularity of the induced metric. Invertibility follows from immersion, with no
additional inverse or determinant-gap hypothesis. -/
theorem contDiffOn_inducedMetric_inv (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ r (fun x ↦ (inducedMetric F x)⁻¹) s := by
  intro x hx
  have hu := (inducedMetric_posDef (himm x hx)).isUnit
  have hi : ContDiffAt ℝ r Ring.inverse (inducedMetric F x) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    hi.comp_contDiffWithinAt x (contDiffOn_inducedMetric_of_le hs hF hr x hx)

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the actual tangent projection
is C^r for a C^(r+1) immersion, as a field of continuous linear maps. -/
theorem contDiffOn_tangentProjection (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ r (tangentProjection F) s := by
  apply contDiffOn_clm_apply.mpr
  intro w
  have hg := contDiffOn_inducedMetric_inv hs hF hr himm
  have hd := contDiffOn_partialDeriv_of_le hs hF hr
  have hsum : ContDiffOn ℝ r (fun x ↦
      ∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j * inner ℝ (partialDeriv F x j) w) •
        partialDeriv F x i) s := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    have hc : ContDiffOn ℝ r (fun x ↦ (inducedMetric F x)⁻¹ i j) s :=
      (matrixEntry i j).contDiff.comp_contDiffOn hg
    exact (hc.mul ((hd j).inner ℝ contDiffOn_const)).smul (hd i)
  exact hsum.congr (fun x hx ↦ tangentProjection_eq_sum (himm x hx) w)

/-- Definition `app:ch_waves:defn:geometry`: the actual normal projection
is C^r for a C^(r+1) immersion, as a field of continuous linear maps. -/
theorem contDiffOn_normalProjection (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ r (normalProjection F) s := by
  have ht := contDiffOn_tangentProjection hs hF hr himm
  apply contDiffOn_clm_apply.mpr
  intro w
  exact (contDiffOn_const.sub (ht.clm_apply contDiffOn_const)).congr
    (fun x _ ↦ normalProjection_eq_sub_tangentProjection F x w)

/-! ## The explicit ambient matrix -/

-- Transfer between coordinate and Frobenius matrix norms.
private def matrixOfEntries (p q : ℕ) :
    (Fin p → Fin q → ℝ) →L[ℝ] Matrix (Fin p) (Fin q) ℝ :=
  { LinearMap.id with cont := continuous_id }

/-- Section 2 (`main:sec:geometry`): the differential matrix has one fewer derivative
than the map, with the Frobenius norm on matrices. -/
theorem contDiffOn_differentialMatrix (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) : ContDiffOn ℝ r (differentialMatrix F) s := by
  apply (matrixOfEntries N n).contDiff.comp_contDiffOn
  exact contDiffOn_pi.mpr fun a ↦ contDiffOn_pi.mpr fun i ↦
    contDiffOn_euclidean.mp (contDiffOn_partialDeriv_of_le hs hF hr i) a

/-- Definition `app:ch_waves:defn:geometry` and equation
`app:ch_waves:eq:ambient-normal-inverse`: the formula `I - dF γ(F)⁻¹ (dF)ᵀ`.
It represents the normal projection wherever `dF` is injective. -/
def normalProjectionMatrix (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    Matrix (Fin N) (Fin N) ℝ :=
  1 - differentialMatrix F x * (inducedMetric F x)⁻¹ * (differentialMatrix F x)ᵀ

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the explicit matrix is the
coordinate matrix of the actual orthogonal normal projection at an immersion point. -/
theorem normalProjection_matrix {x : Euclidean n}
    (himm : Function.Injective (fderiv ℝ F x)) :
    (fun a b ↦ normalProjection F x (EuclideanSpace.single b 1) a) =
      normalProjectionMatrix F x := by
  ext a b
  have ht := congrFun (congrFun (tangentProjection_matrix himm) a) b
  change normalProjection F x (EuclideanSpace.single b 1) a =
    (1 : Matrix (Fin N) (Fin N) ℝ) a b -
      (differentialMatrix F x * (inducedMetric F x)⁻¹ * (differentialMatrix F x)ᵀ) a b
  rw [← ht, normalProjection_eq_sub_tangentProjection]
  simp [Matrix.one_apply]

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the inverse-Gram matrix formula
agrees with the actual normal projection on every ambient vector. -/
theorem normalProjection_eq_matrix_mulVec {x : Euclidean n}
    (himm : Function.Injective (fderiv ℝ F x)) (w : Euclidean N) :
    (fun a ↦ normalProjection F x w a) =
      (normalProjectionMatrix F x).mulVec (fun a ↦ w a) := by
  rw [normalProjectionMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← tangentProjection_eq_matrix_mulVec himm]
  ext a
  simp [normalProjection_eq_sub_tangentProjection]

/-- Definition `app:ch_waves:defn:geometry`: the actual normal-projection matrix
`I - dF γ(F)⁻¹ (dF)ᵀ` is C^r for a C^(r+1) immersion, in the Frobenius norm. -/
theorem contDiffOn_normalProjectionMatrix (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 ≤ m) (himm : IsImmersionOn F s) :
    ContDiffOn ℝ r (normalProjectionMatrix F) s := by
  have hp := contDiffOn_normalProjection hs hF hr himm
  have hc := (matrixOfEntries N N).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr fun a ↦ contDiffOn_pi.mpr fun b ↦
      contDiffOn_euclidean.mp (hp.clm_apply
        (contDiffOn_const (c := EuclideanSpace.single b 1))) a)
  exact hc.congr (fun x hx ↦ (normalProjection_matrix (himm x hx)).symm)

/-! ## The actual second fundamental form -/

/-- Definition `app:ch_waves:defn:geometry`: the actual second fundamental form
is the orthogonal normal projection of the coordinate Hessian. -/
theorem secondFundamentalForm_eq_normalProjection (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i j : Fin n) :
    secondFundamentalForm F x i j =
      normalProjection F x (partialDeriv (fun y ↦ partialDeriv F y j) x i) := rfl

/-- Definition `app:ch_waves:defn:geometry`: the actual second fundamental form
is C^r for a C^(r+2) immersion. Taking all orders equal to ∞ gives smoothness. -/
theorem contDiffOn_secondFundamentalForm (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 + 1 ≤ m) (himm : IsImmersionOn F s) (i j : Fin n) :
    ContDiffOn ℝ r (fun x ↦ secondFundamentalForm F x i j) s := by
  have hr' : r + 1 ≤ m := le_trans (le_self_add) hr
  exact (contDiffOn_normalProjection hs hF hr' himm).clm_apply
    (contDiffOn_partialDeriv_of_le hs (contDiffOn_partialDeriv_of_le hs hF hr j) le_rfl i)

/-- Definition `app:ch_waves:defn:geometry`: the coordinate Hessian projected using
the explicit inverse-Gram formula on the fixed ambient space. -/
def projectedHessian (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (i j : Fin n) : Euclidean N :=
  WithLp.toLp 2 ((normalProjectionMatrix F x).mulVec
    (fun a ↦ partialDeriv (fun y ↦ partialDeriv F y j) x i a))

/-- Definition `app:ch_waves:defn:geometry`: the explicit projected Hessian equals
the actual second fundamental form wherever `dF` is injective. -/
theorem projectedHessian_eq_secondFundamentalForm {x : Euclidean n}
    (himm : Function.Injective (fderiv ℝ F x)) (i j : Fin n) :
    projectedHessian F x i j = secondFundamentalForm F x i j := by
  ext a
  exact (congrFun (normalProjection_eq_matrix_mulVec himm
    (partialDeriv (fun y ↦ partialDeriv F y j) x i)) a).symm

/-- Definition `app:ch_waves:defn:geometry`: the explicit projected Hessian is C^r
for a C^(r+2) immersion and hence smooth for a smooth immersion. -/
theorem contDiffOn_projectedHessian (hs : IsOpen s) (hF : ContDiffOn ℝ m F s)
    (hr : r + 1 + 1 ≤ m) (himm : IsImmersionOn F s) (i j : Fin n) :
    ContDiffOn ℝ r (fun x ↦ projectedHessian F x i j) s :=
  (contDiffOn_secondFundamentalForm hs hF hr himm i j).congr
    (fun x hx ↦ projectedHessian_eq_secondFundamentalForm (himm x hx) i j)

/-! ## Smoothness on the open immersion domain -/

/-- Definition `app:ch_waves:defn:geometry`: the actual normal projection of a smooth
map is smooth on its open immersion domain. -/
theorem contDiffOn_normalProjection_immersionDomain (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (normalProjection F) (immersionDomain F s) :=
  contDiffOn_normalProjection (isOpen_immersionDomain hs (hF.of_le (by simp)))
    (hF.mono (fun _ hx ↦ hx.1)) (by simp) (isImmersionOn_immersionDomain F s)

/-- Equation `app:ch_waves:eq:ambient-normal-inverse`: the normal-projection matrix
of a smooth map is smooth on its open immersion domain. -/
theorem contDiffOn_normalProjectionMatrix_immersionDomain (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (normalProjectionMatrix F) (immersionDomain F s) :=
  contDiffOn_normalProjectionMatrix (isOpen_immersionDomain hs (hF.of_le (by simp)))
    (hF.mono (fun _ hx ↦ hx.1)) (by simp) (isImmersionOn_immersionDomain F s)

/-- Definition `app:ch_waves:defn:geometry`: the actual second fundamental form
of a smooth map is smooth on its open immersion domain. -/
theorem contDiffOn_secondFundamentalForm_immersionDomain (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x ↦ secondFundamentalForm F x i j) (immersionDomain F s) :=
  contDiffOn_secondFundamentalForm (isOpen_immersionDomain hs (hF.of_le (by simp)))
    (hF.mono (fun _ hx ↦ hx.1)) (by simp) (isImmersionOn_immersionDomain F s) i j

end JanetCartan
