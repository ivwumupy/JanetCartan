module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Transversality
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Corank
public import JanetCartan.Geometry.IsometricEmbedding.Reference.DeterminantDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Regularity and tangent incidence for reciprocal cube carriers

Rank, determinant differential, and incidence transversality in reciprocal
coordinates for `app:ch_seed:prop:seed-frozen-menu`, Steps 1 and 3.
The determinant differential is computed directly from reciprocal factorization.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace JanetCartan.CubeCarrier

/-- All-nonzero characteristics have rank `n-1`, as used in
`app:ch_seed:prop:seed-frozen-menu`, Step 1. -/
theorem pencil_rank_of_characteristic {n : ℕ} (hn : 5 ≤ n) {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) :
    (cubePencil r).rank = n - 1 := by
  have hle := finrank_cubePencilKernel_le_one_of_coordinates_ne_zero hr
  have hge : 1 ≤ Module.finrank ℝ (cubePencilKernel r) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hzero
    have hmem : (fun i ↦ reciprocal r i) ∈ cubePencilKernel r := reciprocal_mem_kernel hr hchar
    rw [hzero, Submodule.mem_bot] at hmem
    have hi := congrFun hmem ⟨0, by omega⟩
    exact inv_ne_zero (hr _) hi
  have := cubePencil_rank_add_finrank_kernel r
  omega

/-- Directional differentiation along an affine line, used in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem fderiv_apply_of_line {n : ℕ} {f : Euclidean n → ℝ} {x e : Euclidean n}
    (hf : DifferentiableAt ℝ f x) {a : ℝ}
    (ha : HasDerivAt (fun t : ℝ ↦ f (x + t • e)) a 0) :
    fderiv ℝ f x e = a := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • e) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt 0 hl).unique ha

/-- The explicit nonzero scalar multiple of the reciprocal quadratic normal
in `app:ch_seed:prop:seed-frozen-menu`, Steps 1 and 3. -/
theorem determinant_differential {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) (e : Euclidean n) :
    fderiv ℝ cubeDeterminant r e =
      ((∏ i, r i) * cubeCoefficient n * (∑ i, r i)) *
        (∑ i, e i * quadratic (reciprocal r) i) := by
  have hc (i : Fin n) : HasDerivAt (fun t : ℝ ↦ r i + t * e i) (e i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e i)).const_add (r i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hc i)
  have hi := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    (hc i).inv (by simpa using hr i))
  have hp : DifferentiableAt ℝ (fun t : ℝ ↦ ∏ i, (r i + t * e i)) 0 := by
    fun_prop
  have hd := hp.hasDerivAt.fun_mul (((hs.const_mul (cubeCoefficient n)).fun_mul hi).const_sub 1)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, r i + t * e i ≠ 0 :=
    eventually_all.mpr (fun i ↦ (hc i).continuousAt.eventually_ne (by simpa using hr i))
  have heq : (fun t : ℝ ↦ cubeDeterminant (r + t • e)) =ᶠ[𝓝 0]
      (fun t ↦ (∏ i, (r i + t * e i)) *
        (1 - cubeCoefficient n * (∑ i, (r i + t * e i)) *
          (∑ i, (r i + t * e i)⁻¹))) := by
    filter_upwards [hev] with t ht
    exact determinant_factor (r := r + t • e) ht
  have hcalc := fderiv_apply_of_line (hasFDerivAt_cubeDeterminant r).differentiableAt
    (hd.congr_of_eventuallyEq heq)
  simp only [Pi.inv_apply, zero_mul, add_zero] at hcalc
  rw [hcalc]
  have hchar' := (determinant_eq_zero_iff hr).mp hchar
  simp only [reciprocal_apply] at hchar'
  rw [hchar', sub_self, mul_zero, zero_add]
  have he (i : Fin n) : -e i / r i ^ 2 = -(e i * (r i)⁻¹ ^ 2) := by
    field_simp
  simp only [he, Finset.sum_neg_distrib]
  change _ = _ * (∑ i, e i * ((r i)⁻¹ ^ 2 -
    cubeCoefficient n * (∑ j, (r j)⁻¹) ^ 2))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hc' : cubeCoefficient n * (∑ i, r i) *
      (cubeCoefficient n * (∑ i, (r i)⁻¹)^2) =
      cubeCoefficient n * (∑ i, (r i)⁻¹) := by
    calc
      _ = (cubeCoefficient n * (∑ i, r i) * (∑ i, (r i)⁻¹)) *
        (cubeCoefficient n * (∑ i, (r i)⁻¹)) := by ring
      _ = _ := by rw [hchar', one_mul]
  linear_combination (∏ i, r i) * (∑ i, e i) * hc'

/-- The coordinate quadratic vector equals the stress contraction used in
`app:ch_seed:prop:seed-frozen-menu`. -/
theorem quadratic_eq_cubeQuadraticContraction {n : ℕ} (r : Euclidean n) :
    quadratic r = cubeQuadraticContraction r := by
  ext i
  exact (cubeQuadraticContraction_apply r i).symm

/-- The reciprocal quadratic vector is the characteristic normal, with an
explicit scalar factor (`app:ch_seed:prop:seed-frozen-menu`, Steps 1 and 3). -/
theorem determinant_differential_eq_innerSL {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) :
    fderiv ℝ cubeDeterminant r =
      ((∏ i, r i) * cubeCoefficient n * (∑ i, r i)) • innerSL ℝ (quadratic (reciprocal r)) := by
  ext e
  rw [determinant_differential hr hchar]
  simp [PiLp.inner_apply, mul_comm]

/-- The normal multiplier is nonzero on the all-nonzero characteristic locus
(`app:ch_seed:prop:seed-frozen-menu`, Step 1). -/
theorem determinant_normal_multiplier_ne_zero {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0) :
    (∏ i, r i) * cubeCoefficient n * (∑ i, r i) ≠ 0 := by
  have h := (determinant_eq_zero_iff hr).mp hchar
  have hc : cubeCoefficient n * (∑ i, r i) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    norm_num at h
  simpa only [mul_assoc] using mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hr i)) hc

/-- Nonzero reciprocal quadratic normal implies regularity of the
characteristic (`app:ch_seed:prop:seed-frozen-menu`, Steps 1–3). -/
theorem regular_of_quadratic_reciprocal_ne_zero {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0)
    (hq : quadratic (reciprocal r) ≠ 0) : fderiv ℝ cubeDeterminant r ≠ 0 := by
  intro hz
  apply hq
  ext i
  have h := determinant_differential hr hchar (EuclideanSpace.single i 1)
  rw [hz] at h
  simpa using (mul_eq_zero.mp (by simpa using h.symm)).resolve_left
    (determinant_normal_multiplier_ne_zero hr hchar)

/-- Incidence differential in reciprocal coordinates is `2 M₀(k)r`, as in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem incidence_differential {n : ℕ} (k r e : Euclidean n) :
    fderiv ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic x i) r e =
      2 * (∑ i, e i * (cubePencil k).mulVec (fun j ↦ r j) i) := by
  have hcoord (i : Fin n) : Differentiable ℝ (fun x : Euclidean n ↦ x i) :=
    (ContinuousLinearMap.proj i |>.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap).differentiable
  have hf : Differentiable ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic x i) := by
    unfold quadratic
    fun_prop
  have hc (i : Fin n) : HasDerivAt (fun t : ℝ ↦ r i + t * e i) (e i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e i)).const_add (r i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hc i)
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    (((hc i).pow 2).sub ((hs.pow 2).const_mul (cubeCoefficient n))).const_mul (k i))
  have heq := fderiv_apply_of_line (hf r) hd
  rw [heq]
  simp only [zero_mul, add_zero, Nat.add_one_sub_one, pow_one, pencil_mulVec_apply,
    mul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- Incidence is transverse to the characteristic hypersurface in reciprocal
coordinates: its differential is nonzero on a characteristic tangent vector
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem exists_transverse_tangent {n : ℕ} {k s r : Euclidean n}
    (hk : k ≠ 0) (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hchar : cubeDeterminant r = 0)
    (hdet : (∑ i, s i * quadratic (reciprocal r) i) ≠ 0) :
    ∃ e : Euclidean n, fderiv ℝ cubeDeterminant r e = 0 ∧
      fderiv ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic x i) r e ≠ 0 := by
  have hg := incidence_gradient_ne_zero hk hs hr hker hchar hdet
  obtain ⟨i, hi⟩ : ∃ i, (cubePencil k).mulVec (fun j ↦ r j) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (funext h)
  let a := quadratic (reciprocal r) i / (∑ j, s j * quadratic (reciprocal r) j)
  let e := EuclideanSpace.single i 1 - a • s
  refine ⟨e, ?_, ?_⟩
  · rw [determinant_differential hr hchar]
    have he : (∑ j, e j * quadratic (reciprocal r) j) = 0 := by
      simp only [e, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      simp [a, hdet]
    rw [he, mul_zero]
  · rw [incidence_differential]
    have he : (∑ j, e j * (cubePencil k).mulVec (fun l ↦ r l) j) =
        (cubePencil k).mulVec (fun l ↦ r l) i := by
      simp only [e, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
        stress_annihilates_incidence_gradient hker, mul_zero, sub_zero]
      simp
    rw [he]
    exact mul_ne_zero (by norm_num) hi

end JanetCartan.CubeCarrier
