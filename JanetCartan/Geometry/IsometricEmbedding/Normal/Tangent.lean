module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import JanetCartan.Geometry.IsometricEmbedding.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Metric pairing and smoothness of the tangential lift

For the tangential part of `main:eq:tangent-normal`, raising a covector by the
induced metric and applying the differential recovers that covector under metric
pairing. The induced metric is positive definite wherever the differential is
injective. On an open immersion domain its inverse, and hence the tangential
lift of a smooth covector field, are smooth. Matrix norms are Frobenius norms.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- For `main:eq:tangent-normal`, an injective differential has positive definite
induced metric, since the coordinate derivatives form a linearly independent family. -/
theorem inducedMetric_posDef_of_injective_fderiv {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : Function.Injective (fderiv ℝ F x)) : (inducedMetric F x).PosDef := by
  change (Matrix.gram ℝ (partialDeriv F x)).PosDef
  apply Matrix.posDef_gram_of_linearIndependent
  simpa only [Function.comp_def, EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis,
    ContinuousLinearMap.coe_coe, partialDeriv] using!
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map'
      (fderiv ℝ F x).toLinearMap (LinearMap.ker_eq_bot.mpr hF)

/-- The tangential lift in `main:eq:tangent-normal` pairs with each coordinate
derivative to recover the corresponding covector component. -/
theorem inner_partialDeriv_tangentLift {n N : ℕ}
    {F : Euclidean n → Euclidean N} (u : Euclidean n → Euclidean n)
    {x : Euclidean n} (hF : Function.Injective (fderiv ℝ F x)) (i : Fin n) :
    inner ℝ (partialDeriv F x i) (tangentLift F u x) = u x i := by
  have hunit := (Matrix.isUnit_iff_isUnit_det (inducedMetric F x)).mp
    (inducedMetric_posDef_of_injective_fderiv hF).isUnit
  have hm := congrFun (congrFun ((inducedMetric F x).mul_nonsing_inv hunit) i)
  simp only [tangentLift, inner_sum, inner_smul_right]
  calc
    (∑ k, ∑ j, ((inducedMetric F x)⁻¹ k j * u x j) *
        inner ℝ (partialDeriv F x i) (partialDeriv F x k)) =
        ∑ j, (∑ k, inducedMetric F x i k * (inducedMetric F x)⁻¹ k j) * u x j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [inducedMetric]
      ring
    _ = u x i := by
      simp only [← Matrix.mul_apply, hm, Matrix.one_apply]
      simp

/-- The covector recovery identity of `main:eq:tangent-normal` on an immersion domain. -/
theorem inner_partialDeriv_tangentLift_eqOn {n N : ℕ}
    {F : Euclidean n → Euclidean N} (u : Euclidean n → Euclidean n)
    {s : Set (Euclidean n)} (himm : IsImmersionOn F s) (i : Fin n) :
    EqOn (fun x ↦ inner ℝ (partialDeriv F x i) (tangentLift F u x))
      (fun x ↦ u x i) s := by
  intro x hx
  exact inner_partialDeriv_tangentLift u (himm x hx) i

/-- The coordinate derivatives used in `main:eq:tangent-normal` are smooth on
an open domain where the immersion map is smooth. -/
theorem contDiffOn_partialDeriv {n N : ℕ} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x ↦ partialDeriv F x i) s := by
  exact contDiffOn_partialDeriv_of_le hs hF (by simp) i

/-- The induced metric in `main:eq:tangent-normal` is smooth on the open domain
of a smooth map, with the chosen Frobenius matrix norm. -/
theorem contDiffOn_inducedMetric {n N : ℕ} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (inducedMetric F) s := by
  exact contDiffOn_inducedMetric_of_le hs hF (by simp)

/-- The inverse induced metric used to raise covectors in `main:eq:tangent-normal`
is smooth on an open domain of a smooth immersion. -/
theorem contDiffOn_inverse_inducedMetric {n N : ℕ} {F : Euclidean n → Euclidean N}
    {s : Set (Euclidean n)} (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : IsImmersionOn F s) :
    ContDiffOn ℝ ∞ (fun x ↦ (inducedMetric F x)⁻¹) s := by
  intro x hx
  have hu := (inducedMetric_posDef_of_injective_fderiv (himm x hx)).isUnit
  have hi : ContDiffAt ℝ ∞ Ring.inverse (inducedMetric F x) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    hi.comp_contDiffWithinAt x (contDiffOn_inducedMetric hs hF x hx)

/-- The tangential lift in `main:eq:tangent-normal` is smooth for a smooth
covector field and a smooth immersion on an open coordinate domain. -/
theorem contDiffOn_tangentLift {n N : ℕ} {F : Euclidean n → Euclidean N}
    {u : Euclidean n → Euclidean n} {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) : ContDiffOn ℝ ∞ (tangentLift F u) s := by
  have hg := contDiffOn_inverse_inducedMetric hs hF himm
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  let L : MetricTensor n →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i)
  let C : MetricTensor n →L[ℝ] ℝ := ⟨L, L.continuous_of_finiteDimensional⟩
  have hc : ContDiffOn ℝ ∞ (fun x ↦ (inducedMetric F x)⁻¹ i j) s :=
    C.contDiff.comp_contDiffOn hg
  exact (hc.mul ((contDiffOn_piLp 2).mp hu j)).smul (contDiffOn_partialDeriv hs hF i)

end JanetCartan
