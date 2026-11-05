module

public import JanetCartan.Geometry.IsometricEmbedding.Coordinates.Linear
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs

import Mathlib.Tactic.Ring

/-!
# Normalizing local coordinates and undoing dilations

The coordinate reductions in Section 2 (`main:prop:seed`, `main:eq:normalized`)
and the return to the original metric in Section 9. The dilation of a metric
field `scaledMetric g r` is `g(r x)`; it differs by a factor of `r²` from the
pullback under the dilation. The compensating target dilation cancels this factor.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan

/-- Section 2, `main:prop:seed`: the coordinate chain rule. -/
theorem partialDeriv_comp_coordinateMap {n N : ℕ} {F : Euclidean n → Euclidean N}
    (A : MetricTensor n) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (coordinateMap A x)) (i : Fin n) :
    partialDeriv (F ∘ coordinateMap A) x i =
      ∑ k, A k i • partialDeriv F (coordinateMap A x) k := by
  have hvec : coordinateMap A (EuclideanSpace.single i 1) =
      ∑ k, A k i • EuclideanSpace.single k 1 := by
    ext j
    simp [coordinateMap_apply, Pi.single_apply]
  simp only [partialDeriv, fderiv_comp x hF (coordinateMap A).differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, hvec, map_sum, map_smul]

/-- Section 2, `main:prop:seed`: the induced metric transforms by tensor pullback. -/
theorem inducedMetric_comp_coordinateMap {n N : ℕ} {F : Euclidean n → Euclidean N}
    (A : MetricTensor n) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (coordinateMap A x)) :
    inducedMetric (F ∘ coordinateMap A) x = coordinatePullback (inducedMetric F) A x := by
  ext i j
  simp only [inducedMetric, partialDeriv_comp_coordinateMap A hF, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, conj_trivial, coordinatePullback, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Section 2, `main:prop:seed`: local metric equations pull back along linear maps. -/
theorem isIsometricOn_coordinatePullback {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hiso : IsIsometricOn g F U)
    (A : MetricTensor n) :
    IsIsometricOn (coordinatePullback g A) (F ∘ coordinateMap A) (coordinateMap A ⁻¹' U) := by
  intro x hx
  rw [inducedMetric_comp_coordinateMap A
    ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))]
  simp only [coordinatePullback, hiso hx]

/-- Section 2, `main:prop:seed`: a solution for the normalized metric gives a
smooth solution for the original metric on the inverse coordinate domain. -/
theorem restore_coordinates {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {V : Set (Euclidean n)}
    (A : MetricTensor n) (hA : IsUnit A) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hiso : IsIsometricOn (coordinatePullback g A) F V) :
    ContDiffOn ℝ ∞ (F ∘ coordinateMap A⁻¹) (coordinateMap A⁻¹ ⁻¹' V) ∧
      IsIsometricOn g (F ∘ coordinateMap A⁻¹) (coordinateMap A⁻¹ ⁻¹' V) := by
  refine ⟨hF.comp (coordinateMap A⁻¹).contDiff.contDiffOn (fun _ hx ↦ hx), ?_⟩
  simpa only [coordinatePullback_inv g A hA] using
    isIsometricOn_coordinatePullback hV hF hiso A⁻¹

/-- Equation `main:eq:normalized`: the normalized source and target dilation. -/
def normalizedRescaling {n N : ℕ} (F : Euclidean n → Euclidean N) (r : ℝ) :
    Euclidean n → Euclidean N := fun x ↦ r⁻¹ • (F (r • x) - F 0)

/-- Equation `main:eq:normalized`: the rescaled reference fixes zero. -/
@[simp] theorem normalizedRescaling_zero {n N : ℕ} (F : Euclidean n → Euclidean N)
    (r : ℝ) : normalizedRescaling F r 0 = 0 := by simp [normalizedRescaling]

/-- Equation `main:eq:normalized`: differentiating the normalized dilation cancels
its source and target scale factors. -/
theorem fderiv_normalizedRescaling {n N : ℕ} {F : Euclidean n → Euclidean N}
    {r : ℝ} (hr : r ≠ 0) {x : Euclidean n} (hF : DifferentiableAt ℝ F (r • x)) :
    fderiv ℝ (normalizedRescaling F r) x = fderiv ℝ F (r • x) := by
  have hlin : HasFDerivAt (fun y : Euclidean n ↦ r • y)
      (r • ContinuousLinearMap.id ℝ (Euclidean n)) x :=
    (hasFDerivAt_id x).const_smul r
  have h := ((hF.hasFDerivAt.comp x hlin).sub_const (F 0)).const_smul r⁻¹
  have heq : r⁻¹ • ((fderiv ℝ F (r • x)).comp (r • ContinuousLinearMap.id ℝ (Euclidean n))) =
      fderiv ℝ F (r • x) := by
    ext v
    simp [smul_smul, hr]
  rw [heq] at h
  exact h.fderiv

/-- Equation `main:eq:normalized`: the exact induced-metric rescaling formula. -/
theorem inducedMetric_normalizedRescaling {n N : ℕ} {F : Euclidean n → Euclidean N}
    {r : ℝ} (hr : r ≠ 0) {x : Euclidean n} (hF : DifferentiableAt ℝ F (r • x)) :
    inducedMetric (normalizedRescaling F r) x = scaledMetric (inducedMetric F) r x := by
  ext i j
  simp only [inducedMetric, partialDeriv, fderiv_normalizedRescaling hr hF, scaledMetric]

/-- Equation `main:eq:normalized`: normalized dilation preserves local smoothness. -/
theorem contDiffOn_normalizedRescaling {n N : ℕ} {F : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hF : ContDiffOn ℝ ∞ F U) (r : ℝ) :
    ContDiffOn ℝ ∞ (normalizedRescaling F r) ((fun x ↦ r • x) ⁻¹' U) :=
  ((hF.comp (contDiff_id.const_smul r).contDiffOn (fun _ hx ↦ hx)).sub
    contDiffOn_const).const_smul r⁻¹

/-- Equation `main:eq:normalized`: scaled targets remain locally smooth. -/
theorem contDiffOn_scaledMetric {n : ℕ} {g : MetricField n} {U : Set (Euclidean n)}
    (hg : ContDiffOn ℝ ∞ g U) (r : ℝ) :
    ContDiffOn ℝ ∞ (scaledMetric g r) ((fun x ↦ r • x) ⁻¹' U) :=
  hg.comp (contDiff_id.const_smul r).contDiffOn (fun _ hx ↦ hx)

/-- Equation `main:eq:normalized`: scaled targets remain positive definite and
smooth, also at the parameter value `r = 0`. -/
theorem isRiemannianMetricOn_scaledMetric {n : ℕ} {g : MetricField n}
    {U : Set (Euclidean n)} (hg : IsRiemannianMetricOn g U) (r : ℝ) :
    IsRiemannianMetricOn (scaledMetric g r) ((fun x ↦ r • x) ⁻¹' U) :=
  ⟨contDiffOn_scaledMetric hg.1 r, fun _ hx ↦ hg.2 _ hx⟩

/-- Equation `main:eq:normalized`: dilation preserves the metric at zero. -/
@[simp] theorem scaledMetric_at_zero {n : ℕ} (g : MetricField n) (r : ℝ) :
    scaledMetric g r 0 = g 0 := by simp [scaledMetric]

/-- Equation `main:eq:normalized`: the zero parameter freezes the metric. -/
@[simp] theorem scaledMetric_zero_parameter {n : ℕ} (g : MetricField n) :
    scaledMetric g 0 = fun _ ↦ g 0 := by funext x; simp [scaledMetric]

/-- Equation `main:eq:normalized`: unit dilation preserves the target. -/
@[simp] theorem scaledMetric_one {n : ℕ} (g : MetricField n) : scaledMetric g 1 = g := by
  funext x
  simp [scaledMetric]

/-- Equation `main:eq:normalized`: combine the fixed scale `ρ` and target scale `s`. -/
theorem scaledMetric_comp {n : ℕ} (g : MetricField n) (r s : ℝ) :
    scaledMetric (scaledMetric g r) s = scaledMetric g (r * s) := by
  funext x
  simp [scaledMetric, smul_smul]

/-- Equation `main:eq:normalized`: scalar matrices act by dilation. -/
@[simp] theorem coordinateMap_smul_one {n : ℕ} (r : ℝ) (x : Euclidean n) :
    coordinateMap (r • (1 : MetricTensor n)) x = r • x := by
  ext i
  simp [coordinateMap_apply, Matrix.smul_apply, Matrix.one_apply]

/-- Equation `main:eq:normalized`: distinguish the tensor pullback from the scaled
target; the former includes the two derivative scale factors. -/
theorem coordinatePullback_smul_one {n : ℕ} (g : MetricField n) (r : ℝ) :
    coordinatePullback g (r • (1 : MetricTensor n)) = r ^ 2 • scaledMetric g r := by
  funext x
  simp [coordinatePullback, Matrix.transpose_smul, scaledMetric, smul_smul, pow_two]

/-- Equation `main:eq:normalized`: metric equations are preserved by the normalized
dilation on the rescaled open domain. -/
theorem isIsometricOn_normalizedRescaling {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hiso : IsIsometricOn g F U) {r : ℝ} (hr : r ≠ 0) :
    IsIsometricOn (scaledMetric g r) (normalizedRescaling F r)
      ((fun x ↦ r • x) ⁻¹' U) := by
  intro x hx
  rw [inducedMetric_normalizedRescaling hr
    ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))]
  exact hiso hx

/-- Section 9 after `main:eq:final-Cr`: undo the target dilation to solve the
original metric equation. The ambient translation fixes the value at zero. -/
theorem restore_scaledMetric {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) {r : ℝ} (hr : r ≠ 0)
    (hiso : IsIsometricOn (scaledMetric g r) F U) :
    ContDiffOn ℝ ∞ (normalizedRescaling F r⁻¹) ((fun x ↦ r⁻¹ • x) ⁻¹' U) ∧
      IsIsometricOn g (normalizedRescaling F r⁻¹) ((fun x ↦ r⁻¹ • x) ⁻¹' U) := by
  refine ⟨contDiffOn_normalizedRescaling hF _, ?_⟩
  have h := isIsometricOn_normalizedRescaling hU hF hiso (inv_ne_zero hr)
  simpa only [scaledMetric_comp, mul_inv_cancel₀ hr, scaledMetric_one] using h

/-- Equation `main:eq:normalized`: dilations preserve open neighborhoods of zero. -/
theorem dilation_preimage_neighborhood {n : ℕ} {U : Set (Euclidean n)}
    (hU : IsOpen U) (h0 : (0 : Euclidean n) ∈ U) (r : ℝ) :
    IsOpen ((fun x : Euclidean n ↦ r • x) ⁻¹' U) ∧
      (0 : Euclidean n) ∈ (fun x ↦ r • x) ⁻¹' U :=
  ⟨hU.preimage (continuous_id.const_smul r), by simpa using h0⟩

/-- Section 9, `main:sec:convergence`: undo both normalization steps. A local
solution for the scaled normalized metric yields a smooth local solution for `g`
on an open neighborhood of zero. -/
theorem restore_normalized_scaledMetric {n N : ℕ} {g : MetricField n}
    {F : Euclidean n → Euclidean N} {V : Set (Euclidean n)}
    (A : MetricTensor n) (hA : IsUnit A) {r : ℝ} (hr : r ≠ 0)
    (hV : IsOpen V) (h0 : (0 : Euclidean n) ∈ V) (hF : ContDiffOn ℝ ∞ F V)
    (hiso : IsIsometricOn (scaledMetric (coordinatePullback g A) r) F V) :
    let W := coordinateMap A⁻¹ ⁻¹' ((fun x ↦ r⁻¹ • x) ⁻¹' V)
    let H := normalizedRescaling F r⁻¹ ∘ coordinateMap A⁻¹
    IsOpen W ∧ (0 : Euclidean n) ∈ W ∧ ContDiffOn ℝ ∞ H W ∧ IsIsometricOn g H W := by
  obtain ⟨hW, hW0⟩ := dilation_preimage_neighborhood hV h0 r⁻¹
  obtain ⟨hH, hmetric⟩ := restore_scaledMetric hV hF hr hiso
  obtain ⟨hsmooth, hisometric⟩ := restore_coordinates A hA hW hH hmetric
  exact ⟨(coordinate_preimage_neighborhood hW hW0 A⁻¹).1,
    (coordinate_preimage_neighborhood hW hW0 A⁻¹).2, hsmooth, hisometric⟩

end JanetCartan
