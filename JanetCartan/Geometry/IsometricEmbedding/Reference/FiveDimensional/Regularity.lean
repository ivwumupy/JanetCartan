module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FiveDimensional.Algebra
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Regularity and incidence transversality

The exceptional carrier in `app:ch_seed:prop:seed-frozen-menu`, Steps 2–3.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiveDimensional

/-- The determinant on a coordinate line through the carrier
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_slice (t : ℝ) :
    cubeDeterminant (carrier + t • EuclideanSpace.single 0 1) = 6 * t + 2 * t ^ 2 := by
  have hu : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  rw [cubeDeterminant_eq]
  norm_num [hu, cubeCoefficient, carrier, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton]
  ring_nf
  norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

/-- The determinant on a coordinate line through the reciprocal carrier
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem reciprocalCarrier_slice (t : ℝ) :
    cubeDeterminant (reciprocalCarrier + t • EuclideanSpace.single 0 1) =
      -(3 / 8) * t - (1 / 4) * t ^ 2 := by
  have hu : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  rw [cubeDeterminant_eq]
  norm_num [hu, cubeCoefficient, reciprocalCarrier, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton]
  ring_nf
  norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

private theorem determinant_differentiable : Differentiable ℝ (@cubeDeterminant 5) := by
  change Differentiable ℝ (fun x : Euclidean 5 ↦ cubeDeterminant x)
  simp_rw [cubeDeterminant_eq]
  have hcoord (i : Fin 5) : Differentiable ℝ (fun x : Euclidean 5 ↦ x i) :=
    (ContinuousLinearMap.proj i |>.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).toContinuousLinearMap).differentiable
  fun_prop

private theorem fderiv_apply_of_slice (f : Euclidean 5 → ℝ) (x v : Euclidean 5)
    (hf : DifferentiableAt ℝ f x) (d : ℝ)
    (hslice : HasDerivAt (fun t : ℝ ↦ f (x + t • v)) d 0) :
    fderiv ℝ f x v = d := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hder : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact (hder.comp_hasDerivAt 0 hline).unique hslice

private theorem regular_of_slice (x : Euclidean 5) (d : ℝ) (hd : d ≠ 0)
    (hslice : HasDerivAt (fun t : ℝ ↦ cubeDeterminant
      (x + t • EuclideanSpace.single 0 1)) d 0) :
    fderiv ℝ cubeDeterminant x ≠ 0 := by
  intro hzero
  have heq := fderiv_apply_of_slice cubeDeterminant x (EuclideanSpace.single 0 1)
    (determinant_differentiable x) d hslice
  rw [hzero] at heq
  exact hd heq.symm

/-- The carrier is a regular point of the characteristic hypersurface
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem carrier_regular : fderiv ℝ cubeDeterminant carrier ≠ 0 := by
  apply regular_of_slice carrier 6 (by norm_num)
  simp_rw [carrier_slice]
  convert ((hasDerivAt_id (0 : ℝ)).const_mul 6).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2) using 1 <;> norm_num
  rfl

/-- The reciprocal carrier is a regular characteristic point
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem reciprocalCarrier_regular : fderiv ℝ cubeDeterminant reciprocalCarrier ≠ 0 := by
  apply regular_of_slice reciprocalCarrier (-(3 / 8)) (by norm_num)
  simp_rw [reciprocalCarrier_slice]
  convert ((hasDerivAt_id (0 : ℝ)).const_mul (-(3 / 8))).sub
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (1 / 4)) using 1 <;> norm_num
  rfl

/-- The third coordinate direction is tangent to the characteristic hypersurface
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem reciprocalCarrier_tangent_slice (u : ℝ) :
    cubeDeterminant (reciprocalCarrier + u • EuclideanSpace.single 2 1) = 2 * u ^ 2 := by
  have hu : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  rw [cubeDeterminant_eq]
  norm_num [hu, cubeCoefficient, reciprocalCarrier,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton]
  ring_nf
  norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

/-- The exact nonzero incidence derivative along the characteristic tangent direction
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem incidence_tangent_slice (t u : ℝ) :
    (∑ i, (t • node) i * quadratic
      (reciprocalCarrier + u • EuclideanSpace.single 2 1) i) = -2 * t * u := by
  norm_num [quadratic, reciprocalCarrier, node, Fin.sum_univ_succ]
  ring_nf
  norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

/-- At every nonzero node covector, incidence has nonzero differential on the
characteristic tangent space in reciprocal coordinates
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem reciprocalCarrier_transverse (t : ℝ) (ht : t ≠ 0) :
    ∃ e : Euclidean 5, fderiv ℝ cubeDeterminant reciprocalCarrier e = 0 ∧
      fderiv ℝ (fun x : Euclidean 5 ↦ ∑ i, (t • node) i * quadratic x i)
        reciprocalCarrier e ≠ 0 := by
  refine ⟨EuclideanSpace.single 2 1, ?_, ?_⟩
  · apply fderiv_apply_of_slice _ _ _ (determinant_differentiable _) 0
    simp_rw [reciprocalCarrier_tangent_slice]
    convert (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2) using 1 <;> norm_num
  · have hf : Differentiable ℝ (fun x : Euclidean 5 ↦
        ∑ i, (t • node) i * quadratic x i) := by
      unfold quadratic
      have hcoord (i : Fin 5) : Differentiable ℝ (fun x : Euclidean 5 ↦ x i) :=
        (ContinuousLinearMap.proj i |>.comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).toContinuousLinearMap).differentiable
      fun_prop
    have hs : HasDerivAt (fun u : ℝ ↦ ∑ i, (t • node) i * quadratic
        (reciprocalCarrier + u • EuclideanSpace.single 2 1) i) (-2 * t) 0 := by
      simp_rw [incidence_tangent_slice]
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-2 * t)
    rw [fderiv_apply_of_slice _ _ _ (hf _) (-2 * t) hs]
    exact mul_ne_zero (by norm_num) ht
end JanetCartan.FiveDimensional

