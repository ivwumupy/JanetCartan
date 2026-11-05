module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Defs
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Linearity of tangential strain

The real linearity used in `app:ch_response:prop:response-ambient` on a chart.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.AmbientResponse

/-- Additivity of the covariant strain in `main:eq:normal-completion`. -/
theorem symmCovariantDeriv_add_apply {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u v : Euclidean n → Euclidean n} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    symmCovariantDeriv F (u + v) x = symmCovariantDeriv F u x + symmCovariantDeriv F v x := by
  ext i j
  have hu' := (differentiableAt_piLp 2).mp hu
  have hv' := (differentiableAt_piLp 2).mp hv
  have hd (a b : Fin n) : partialDeriv (fun y ↦ (u + v) y b) x a =
      partialDeriv (fun y ↦ u y b) x a + partialDeriv (fun y ↦ v y b) x a := by
    change fderiv ℝ ((fun y ↦ u y b) + fun y ↦ v y b) x _ = _
    rw [fderiv_add (hu' b) (hv' b)]
    rfl
  simp only [Matrix.add_apply, symmCovariantDeriv]
  rw [hd, hd]
  simp only [Pi.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- Real homogeneity of the covariant strain in `main:eq:normal-completion`. -/
theorem symmCovariantDeriv_smul_apply {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → Euclidean n} {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (a : ℝ) :
    symmCovariantDeriv F (a • u) x = a • symmCovariantDeriv F u x := by
  ext i j
  have hu' := (differentiableAt_piLp 2).mp hu
  have hd (i j : Fin n) : partialDeriv (fun y ↦ (a • u) y j) x i =
      a * partialDeriv (fun y ↦ u y j) x i := by
    change fderiv ℝ (a • fun y ↦ u y j) x _ = _
    rw [fderiv_const_smul (hu' j)]
    rfl
  simp only [Matrix.smul_apply, smul_eq_mul, symmCovariantDeriv]
  rw [hd, hd]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

/-- Additivity of the tangential lift in `main:eq:normal-completion`. -/
theorem tangentLift_add {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u v : Euclidean n → Euclidean n) : tangentLift F (u + v) =
      tangentLift F u + tangentLift F v := by
  funext x
  simp [tangentLift, mul_add, add_smul, Finset.sum_add_distrib]

/-- Real homogeneity of the tangential lift in `main:eq:normal-completion`. -/
theorem tangentLift_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (a : ℝ) : tangentLift F (a • u) =
      a • tangentLift F u := by
  funext x
  simp [tangentLift, Finset.smul_sum, smul_smul, mul_left_comm]

end JanetCartan.AmbientResponse
