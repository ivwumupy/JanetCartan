module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputCoordinates
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Orthogonal transfer of the literal sampling input

The SAME `canonicalInputCoordinates` is an orthogonal linear isometry. Its
Jacobian is one in absolute value, and input composition preserves every joint
spatial jet and its parameter derivative. These identities are consumed by the
actual `UniformNormalData` construction for
`app:ch_waves:eq:sampling-operator-bounds`; they supply no missing raw-family
coefficient budget and make no new chart choice.
-/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Metric
open scoped ContDiff
@[expose] public noncomputable section
namespace JanetCartan.Sampling.RawKernel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison ContinuumRow ContinuumRow.CanonicalConic
open ContinuumRow.CanonicalCarrier
open MeanNormalBound.NormalizedFullPhase

/-- The literal insertion `(s,θ)` with its Euclidean product norm, used by
`app:ch_waves:eq:sampling-prefix-normal`. -/
def fullInputCoordinateIsometry (m : ℕ) :
    WithLp 2 (ℝ × Euclidean m) ≃ₗᵢ[ℝ] Euclidean (m + 1) where
  toEquiv := (WithLp.equiv 2 (ℝ × Euclidean m)).trans (fullInputCoordinates m).toEquiv
  map_add' u v := by
    change fullInputCoordinates m (u.ofLp + v.ofLp) =
      fullInputCoordinates m u.ofLp + fullInputCoordinates m v.ofLp
    rw [fullInputCoordinates_apply, fullInputCoordinates_apply, fullInputCoordinates_apply]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  map_smul' a u := by
    change fullInputCoordinates m (a • u.ofLp) = a • fullInputCoordinates m u.ofLp
    rw [fullInputCoordinates_apply, fullInputCoordinates_apply]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  norm_map' u := by
    change ‖fullInputCoordinates m u.ofLp‖ = ‖u‖
    rw [fullInputCoordinates_apply]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, WithLp.prod_norm_sq_eq_of_L2, Fin.sum_univ_succ]
    rw [EuclideanSpace.norm_sq_eq]
    rfl

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The retained canonical input change is orthogonal. This is the SAME map
as `canonicalInputCoordinates`, not an independently selected chart
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def canonicalInputIsometry : Euclidean (m + 1) ≃ₗᵢ[ℝ] Euclidean (m + 1) :=
  (fullInputCoordinateIsometry m).symm.trans (physicalCoordinates T).symm

/-- Pointwise identification with the published measurable input change
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalInputIsometry_apply (u : Euclidean (m + 1)) :
    canonicalInputIsometry T u = canonicalInputCoordinates T u := rfl

/-- The exact input Jacobian introduces no density factor in the full normal
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem abs_det_canonicalInputIsometry :
    |(canonicalInputIsometry T).toLinearEquiv.toLinearMap.det| = 1 := by
  rw [← LinearMap.normDet_eq_abs_det]
  exact (canonicalInputIsometry T).toLinearIsometry.normDet_eq_one

/-- The input differential determinant is preserved under the literal
coordinate substitution, including total derivatives outside the smooth chart.
Consumer: the canonical inverse gap in the actual normal data
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem abs_det_fderiv_comp_canonicalInputCoordinates
    (f : Euclidean (m + 1) → Euclidean (m + 1)) (u : Euclidean (m + 1)) :
    |(fderiv ℝ (fun w ↦ f (canonicalInputCoordinates T w)) u).det| =
      |(fderiv ℝ f (canonicalInputCoordinates T u)).det| := by
  change |(fderiv ℝ (f ∘ (canonicalInputIsometry T).toContinuousLinearEquiv) u).det| = _
  rw [(canonicalInputIsometry T).toContinuousLinearEquiv.comp_right_fderiv]
  change |((fderiv ℝ f (canonicalInputIsometry T u)).toLinearMap.comp
    (canonicalInputIsometry T).toLinearEquiv.toLinearMap).det| = _
  rw [LinearMap.det_comp, abs_mul, abs_det_canonicalInputIsometry, mul_one]
  rfl

/-- Changing only the integration input leaves the averaged physical
gradient at the corresponding point exactly unchanged. The consumer is the
actual full normal's inverse chart (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem averagedGradient_canonicalInputCoordinates
    (φ : Euclidean (m + 1) → Euclidean (m + 1) → ℝ)
    (x y u : Euclidean (m + 1)) :
    NormalComparison.averagedGradient (fun x w ↦ φ x (canonicalInputCoordinates T w)) x y u =
      NormalComparison.averagedGradient φ x y (canonicalInputCoordinates T u) := rfl

/-- The complete averaged-gradient Jacobian has the SAME absolute
determinant in literal input coordinates. This retains both physical positions
and supplies the inverse-gap transfer (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem averagedGradient_abs_det_canonicalInputCoordinates
    (φ : Euclidean (m + 1) → Euclidean (m + 1) → ℝ)
    (x y u : Euclidean (m + 1)) :
    |(fderiv ℝ
      (NormalComparison.averagedGradient (fun x w ↦ φ x (canonicalInputCoordinates T w)) x y)
      u).det| =
      |(fderiv ℝ (NormalComparison.averagedGradient φ x y)
        (canonicalInputCoordinates T u)).det| := by
  have he : NormalComparison.averagedGradient
      (fun x w ↦ φ x (canonicalInputCoordinates T w)) x y =
      fun w ↦ NormalComparison.averagedGradient φ x y (canonicalInputCoordinates T w) :=
    funext (averagedGradient_canonicalInputCoordinates T φ x y)
  rw [he]
  exact abs_det_fderiv_comp_canonicalInputCoordinates T
    (NormalComparison.averagedGradient φ x y) u


/-- Change only the input variable in the joint physical/input derivative
budget, retaining the physical point (`app:ch_waves:eq:sampling-operator-bounds`). -/
def canonicalInputPairIsometry :
    (Euclidean (m + 1) × Euclidean (m + 1)) ≃ₗᵢ[ℝ]
      (Euclidean (m + 1) × Euclidean (m + 1)) where
  toLinearEquiv := (LinearEquiv.refl ℝ _).prodCongr (canonicalInputIsometry T).toLinearEquiv
  norm_map' q := by
    change max ‖q.1‖ ‖canonicalInputIsometry T q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [(canonicalInputIsometry T).norm_map]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every joint input/physical jet has exactly the same norm in the literal
coordinates. In particular this preserves the full `20*(n+1)` reserve of
`UniformNormalData.input_jets` (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_iteratedFDeriv_canonicalInputCoordinates
    (f : Euclidean (m + 1) × Euclidean (m + 1) → E)
    (q : Euclidean (m + 1) × Euclidean (m + 1)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun p ↦ f (p.1, canonicalInputCoordinates T p.2)) q‖ =
      ‖iteratedFDeriv ℝ k f (q.1, canonicalInputCoordinates T q.2)‖ :=
  (canonicalInputPairIsometry T).norm_iteratedFDeriv_comp_right f q k

/-- The parameter derivative of every joint jet is also preserved exactly.
No differentiability premise is needed for this total derivative identity.
The actual primitive budgets are still supplied by the common raw family
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_deriv_iteratedFDeriv_canonicalInputCoordinates
    (f : ℝ → Euclidean (m + 1) × Euclidean (m + 1) → E)
    (ε : ℝ) (q : Euclidean (m + 1) × Euclidean (m + 1)) (k : ℕ) :
    ‖deriv (fun t ↦ iteratedFDeriv ℝ k
      (fun p ↦ f t (p.1, canonicalInputCoordinates T p.2)) q) ε‖ =
      ‖deriv (fun t ↦ iteratedFDeriv ℝ k (f t) (q.1, canonicalInputCoordinates T q.2)) ε‖ := by
  let e := canonicalInputPairIsometry T
  let a := ContinuousLinearEquiv.continuousMultilinearMapCongrLeft E
    (fun _ : Fin k ↦ e.toContinuousLinearEquiv)
  have hj t : iteratedFDeriv ℝ k (fun p ↦ f t (p.1, canonicalInputCoordinates T p.2)) q =
      a (iteratedFDeriv ℝ k (f t) (e q)) := by
    have h := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right (f t)
      uniqueDiffOn_univ (x := q) (Set.mem_univ _) k
    simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at h
    convert! h using 1
  simp_rw [hj]
  change ‖deriv (a ∘ (fun t ↦ iteratedFDeriv ℝ k (f t) (e q))) ε‖ = _
  rw [deriv, a.comp_fderiv]
  change ‖a (deriv (fun t ↦ iteratedFDeriv ℝ k (f t) (e q)) ε)‖ = _
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ _

end JanetCartan.Sampling.RawKernel
