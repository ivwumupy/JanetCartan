module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Tangent
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Christoffel coefficients of an induced metric

The Hessian contraction and tangential strain identity in
`main:eq:tangent-normal` in `paper.tex`. On an open domain, the tangential
lift of a smooth covector field along a smooth immersion has linearized metric
equal to twice its symmetrized covariant derivative for the induced metric.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set

namespace JanetCartan

private theorem differentiableAt_partialDeriv_of_contDiffAt_two {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (i : Fin n) :
    DifferentiableAt ℝ (fun y ↦ partialDeriv F y i) x := by
  exact ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const _)

/-- The Christoffel coefficients of the first kind are Hessian contractions, as used
in the Gauss formula `main:eq:tangent-normal`. -/
theorem inducedMetric_christoffel_firstKind {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (i j k : Fin n) :
    (partialDeriv (fun y ↦ inducedMetric F y j k) x i +
      partialDeriv (fun y ↦ inducedMetric F y i k) x j -
      partialDeriv (fun y ↦ inducedMetric F y i j) x k) / 2 =
      inner ℝ (partialDeriv (fun y ↦ partialDeriv F y j) x i) (partialDeriv F x k) := by
  rw [partialDeriv_inducedMetric_apply hF j k i,
    partialDeriv_inducedMetric_apply hF i k j,
    partialDeriv_inducedMetric_apply hF i j k,
    partialDeriv_partialDeriv_comm hF j i,
    partialDeriv_partialDeriv_comm hF k j,
    partialDeriv_partialDeriv_comm hF k i,
    real_inner_comm (partialDeriv (fun y ↦ partialDeriv F y k) x i)]
  ring

/-- Raising the index in the Hessian contraction gives the induced Christoffel
coefficients (`main:eq:tangent-normal`). -/
theorem christoffel_eq_hessian_contraction {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (i j k : Fin n) :
    christoffel F x i j k =
      ∑ l, (inducedMetric F x)⁻¹ k l *
        inner ℝ (partialDeriv (fun y ↦ partialDeriv F y j) x i) (partialDeriv F x l) := by
  unfold christoffel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← inducedMetric_christoffel_firstKind hF i j l]
  ring

/-- Contracting the Hessian with the raised covector gives the Christoffel term
in `main:eq:tangent-normal`. This algebraic identity does not require invertibility. -/
theorem inner_hessian_tangentLift {n N : ℕ}
    {F : Euclidean n → Euclidean N} (u : Euclidean n → Euclidean n)
    {x : Euclidean n} (hF : ContDiffAt ℝ 2 F x) (i j : Fin n) :
    inner ℝ (partialDeriv (fun y ↦ partialDeriv F y j) x i) (tangentLift F u x) =
      ∑ k, christoffel F x i j k * u x k := by
  have hsymm : (inducedMetric F x)⁻¹.IsSymm :=
    (Matrix.IsSymm.ext fun a b ↦ real_inner_comm _ _).inv
  simp only [tangentLift, inner_sum, inner_smul_right,
    christoffel_eq_hessian_contraction hF, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hsymm.apply k l]
  ring

/-- Differentiating the covector obtained by pairing an ambient field with `dF`
expresses its strain in terms of the Hessian (`main:eq:tangent-normal`). -/
theorem linearizedMetric_eq_of_pairing {n N : ℕ}
    {F Y : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {x : Euclidean n} (hF : ContDiffAt ℝ 2 F x)
    (hY : DifferentiableAt ℝ Y x)
    (hpair : ∀ᶠ y in nhds x, ∀ k, inner ℝ (partialDeriv F y k) (Y y) = u y k)
    (i j : Fin n) :
    linearizedMetric F Y x i j =
      partialDeriv (fun y ↦ u y j) x i + partialDeriv (fun y ↦ u y i) x j -
        2 * inner ℝ (partialDeriv (fun y ↦ partialDeriv F y j) x i) (Y x) := by
  have hdiff (a b : Fin n) :
      partialDeriv (fun y ↦ u y b) x a =
        inner ℝ (partialDeriv F x b) (partialDeriv Y x a) +
        inner ℝ (partialDeriv (fun y ↦ partialDeriv F y b) x a) (Y x) := by
    have heq : (fun y ↦ inner ℝ (partialDeriv F y b) (Y y)) =ᶠ[nhds x]
        (fun y ↦ u y b) := hpair.mono fun y hy ↦ hy b
    rw [partialDeriv, ← heq.fderiv_eq]
    exact fderiv_inner_apply ℝ
      (differentiableAt_partialDeriv_of_contDiffAt_two hF b) hY _
  rw [hdiff i j, hdiff j i, partialDeriv_partialDeriv_comm hF j i]
  simp only [linearizedMetric, real_inner_comm (partialDeriv Y x i)]
  ring

/-- The tangential contribution in `main:eq:tangent-normal`: the linearized metric
of the tangential lift is twice the symmetrized covariant derivative for the
induced metric, on an open domain of a smooth immersion. -/
theorem linearizedMetric_tangentLift {n N : ℕ}
    {F : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {s : Set (Euclidean n)} (hs : IsOpen s)
    (hF : ContDiffOn ℝ ∞ F s) (hu : ContDiffOn ℝ ∞ u s)
    (himm : IsImmersionOn F s) :
    EqOn (linearizedMetric F (tangentLift F u)) (2 • symmCovariantDeriv F u) s := by
  intro x hx
  have hFx : ContDiffAt ℝ 2 F x :=
    ((hF x hx).contDiffAt (hs.mem_nhds hx)).of_le (by simp)
  have hYx : DifferentiableAt ℝ (tangentLift F u) x :=
    (((contDiffOn_tangentLift hs hF hu himm) x hx).contDiffAt
      (hs.mem_nhds hx)).differentiableAt (by simp)
  have hpair : ∀ᶠ y in nhds x, ∀ k,
      inner ℝ (partialDeriv F y k) (tangentLift F u y) = u y k :=
    Filter.Eventually.mono (hs.mem_nhds hx)
      fun y hy k ↦ inner_partialDeriv_tangentLift u (himm y hy) k
  ext i j
  simp only [two_smul, Pi.add_apply, Matrix.add_apply]
  rw [linearizedMetric_eq_of_pairing hFx hYx hpair, inner_hessian_tangentLift u hFx]
  simp only [symmCovariantDeriv]
  ring

end JanetCartan
