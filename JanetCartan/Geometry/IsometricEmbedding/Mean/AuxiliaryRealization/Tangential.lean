module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Christoffel

/-!
# The physical tangential realization of a covector

The geometric step of `app:ch_background:prop:bg-mixed-physical`. For a smooth
covector `u`, the field `½ dG g_G⁻¹ u` has full strain `symmCovariantDeriv G u`.
The final physical cutoff contributes an explicit term containing no derivative
of `u`. Construction of `u` from the continuum adjoint and its Sobolev estimates
are separate analytic steps, not hypotheses of a claimed realization theorem.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.AuxiliaryRealization

variable {n N : ℕ}

/-- The covector-raising factor in `app:ch_background:eq:bg-Vaux`, before
specializing `u` to the smoothed source-cut image component. -/
def tangentialField (G : Euclidean n → Euclidean N) (u : Euclidean n → Euclidean n) :
    Euclidean n → Euclidean N :=
  (1 / 2 : ℝ) • tangentLift G u

/-- Metric pairing for the half tangential lift in `app:ch_background:eq:bg-Vaux`. -/
theorem inner_partialDeriv_tangentialField
    {G : Euclidean n → Euclidean N} (u : Euclidean n → Euclidean n)
    {x : Euclidean n} (hG : Function.Injective (fderiv ℝ G x)) (i : Fin n) :
    inner ℝ (partialDeriv G x i) (tangentialField G u x) = (1 / 2 : ℝ) * u x i := by
  simp only [tangentialField, Pi.smul_apply, inner_smul_right,
    inner_partialDeriv_tangentLift u hG]

/-- Smoothness of the physical covector lift in `app:ch_background:eq:bg-Vaux`. -/
theorem contDiffOn_tangentialField
    {G : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W)
    (hG : ContDiffOn ℝ ∞ G W) (hu : ContDiffOn ℝ ∞ u W)
    (himm : IsImmersionOn G W) : ContDiffOn ℝ ∞ (tangentialField G u) W :=
  contDiffOn_const.smul (contDiffOn_tangentLift hW hG hu himm)

/-- The full strain identity used in `app:ch_background:prop:bg-mixed-physical`,
valid on the entire open immersion domain, before applying the reduced row. -/
theorem linearizedMetric_tangentialField
    {G : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W)
    (hG : ContDiffOn ℝ ∞ G W) (hu : ContDiffOn ℝ ∞ u W)
    (himm : IsImmersionOn G W) :
    EqOn (linearizedMetric G (tangentialField G u)) (symmCovariantDeriv G u) W := by
  intro x hx
  have hd : DifferentiableAt ℝ (tangentLift G u) x :=
    (((contDiffOn_tangentLift hW hG hu himm) x hx).contDiffAt
      (hW.mem_nhds hx)).differentiableAt (by simp)
  have hstrain := linearizedMetric_tangentLift hW hG hu himm hx
  ext i j
  have hij := congrFun (congrFun hstrain i) j
  simp only [two_smul, Pi.add_apply, Matrix.add_apply] at hij
  simp only [linearizedMetric, partialDeriv, tangentialField,
    fderiv_const_smul hd, smul_apply,
    inner_smul_right, real_inner_smul_left]
  change (1 / 2 : ℝ) * inner ℝ (partialDeriv G x i) (partialDeriv (tangentLift G u) x j) +
    (1 / 2 : ℝ) * inner ℝ (partialDeriv (tangentLift G u) x i) (partialDeriv G x j) = _
  change inner ℝ (partialDeriv G x i) (partialDeriv (tangentLift G u) x j) +
    inner ℝ (partialDeriv (tangentLift G u) x i) (partialDeriv G x j) = _ at hij
  linarith

/-- The final physical cutoff of `app:ch_background:prop:bg-mixed-physical` adds
only a term of order zero in the realized covector. This is the full tensor
identity, including the derivative of the final cutoff. -/
theorem linearizedMetric_cutoff_tangentialField
    {G : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W)
    (hG : ContDiffOn ℝ ∞ G W) (hu : ContDiffOn ℝ ∞ u W)
    (himm : IsImmersionOn G W) {χ : Euclidean n → ℝ}
    {x : Euclidean n} (hx : x ∈ W) (hχ : DifferentiableAt ℝ χ x) (i j : Fin n) :
    linearizedMetric G (fun y ↦ χ y • tangentialField G u y) x i j =
      χ x * symmCovariantDeriv G u x i j +
        (partialDeriv χ x i * u x j + partialDeriv χ x j * u x i) / 2 := by
  have hd : DifferentiableAt ℝ (tangentialField G u) x :=
    (((contDiffOn_tangentialField hW hG hu himm) x hx).contDiffAt
      (hW.mem_nhds hx)).differentiableAt (by simp)
  have hderiv (k : Fin n) :
      partialDeriv (fun y ↦ χ y • tangentialField G u y) x k =
        partialDeriv χ x k • tangentialField G u x +
          χ x • partialDeriv (tangentialField G u) x k := by
    simpa only [partialDeriv, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      add_comm] using congrArg
        (fun L : Euclidean n →L[ℝ] Euclidean N ↦ L (EuclideanSpace.single k 1))
        (fderiv_fun_smul hχ hd)
  have hstrain := congrFun (congrFun (linearizedMetric_tangentialField hW hG hu himm hx) i) j
  simp only [linearizedMetric, hderiv, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right,
    inner_partialDeriv_tangentialField u (himm x hx)]
  rw [real_inner_comm (partialDeriv G x j) (tangentialField G u x),
    inner_partialDeriv_tangentialField u (himm x hx)]
  change inner ℝ (partialDeriv G x i) (partialDeriv (tangentialField G u) x j) +
    inner ℝ (partialDeriv (tangentialField G u) x i) (partialDeriv G x j) = _ at hstrain
  rw [← hstrain]
  ring

/-- On an open plateau of the final physical cutoff, the strain is unchanged
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem linearizedMetric_cutoff_tangentialField_on_core
    {G : Euclidean n → Euclidean N} {u : Euclidean n → Euclidean n}
    {W core : Set (Euclidean n)} (hW : IsOpen W) (hcore : IsOpen core)
    (hsub : core ⊆ W) (hG : ContDiffOn ℝ ∞ G W) (hu : ContDiffOn ℝ ∞ u W)
    (himm : IsImmersionOn G W) {χ : Euclidean n → ℝ}
    (hχ : EqOn χ (fun _ ↦ 1) core) :
    EqOn (linearizedMetric G (fun y ↦ χ y • tangentialField G u y))
      (symmCovariantDeriv G u) core := by
  intro x hx
  have heq : (fun y ↦ χ y • tangentialField G u y) =ᶠ[nhds x] tangentialField G u :=
    Filter.Eventually.mono (hcore.mem_nhds hx) fun y hy ↦ by
      dsimp only
      rw [hχ hy, one_smul]
  have hderiv := heq.fderiv_eq (𝕜 := ℝ)
  have hstrain := linearizedMetric_tangentialField hW hG hu himm (hsub hx)
  ext i j
  simpa only [linearizedMetric, partialDeriv, hderiv] using congrFun (congrFun hstrain i) j

end JanetCartan.AuxiliaryRealization
