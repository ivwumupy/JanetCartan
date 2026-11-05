module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth reciprocal normals

The smoothness inputs to quantitative shrinking in Step 3 of
`app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

open scoped ContDiff
namespace JanetCartan.FrozenMenu
open CubeCarrier

/-- The reciprocal quadratic normal is smooth where all carrier coordinates
are nonzero (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem contDiffAt_normal_of_coordinates_ne_zero {n : ℕ} {ξ : Euclidean n}
    (hξ : ∀ i, ξ i ≠ 0) : ContDiffAt ℝ ∞ normal ξ := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℝ ∞ (fun x : Euclidean n ↦
    (x i)⁻¹ ^ 2 - cubeCoefficient n * (∑ j, (x j)⁻¹) ^ 2) ξ
  have hc (j : Fin n) : ContDiffAt ℝ ∞ (fun x : Euclidean n ↦ (x j)⁻¹) ξ :=
    (contDiffAt_piLp_apply (p := 2)).inv (hξ j)
  exact ((hc i).pow 2).sub (contDiffAt_const.mul ((ContDiffAt.sum fun j _ ↦ hc j).pow 2))

/-- Incidence with a fixed covector is smooth at every all-nonzero carrier
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem contDiffAt_incidence_of_coordinates_ne_zero {n : ℕ} (k : Euclidean n)
    {ξ : Euclidean n} (hξ : ∀ i, ξ i ≠ 0) : ContDiffAt ℝ ∞ (incidence k) ξ := by
  have hn := contDiffAt_normal_of_coordinates_ne_zero hξ
  exact ContDiffAt.sum fun i _ ↦ contDiffAt_const.mul
    ((contDiffAt_piLp 2).mp hn i)

end JanetCartan.FrozenMenu
