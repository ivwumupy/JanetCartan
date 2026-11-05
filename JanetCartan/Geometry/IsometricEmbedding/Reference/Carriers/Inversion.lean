module
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Carriers.Regularity
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-!
# Transferring carrier transversality through reciprocal inversion

Coordinate inversion is differentiable on all-nonzero vectors and its
derivatives at reciprocal points are inverse. The determinant transformation
then transfers characteristic tangency and incidence transversality, as in
`app:ch_seed:prop:seed-frozen-menu`, Step 3.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace JanetCartan.CubeCarrier

/-- Differentiable coordinate inversion on all-nonzero vectors, used in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem differentiableAt_reciprocal {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) : DifferentiableAt ℝ reciprocal r := by
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
  have hcoord (i : Fin n) : DifferentiableAt ℝ (fun x : Euclidean n ↦ x i) r :=
    ((ContinuousLinearMap.proj i).comp E.toContinuousLinearMap).differentiableAt
  have h : DifferentiableAt ℝ (fun x : Euclidean n ↦ fun i : Fin n ↦ (x i)⁻¹) r :=
    differentiableAt_pi.mpr (fun i ↦ (hcoord i).inv (hr i))
  exact E.symm.differentiableAt.comp r h

/-- The derivative of inversion is an involution between reciprocal points,
as used to transfer transversality in `app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem reciprocal_differential_comp {n : ℕ} {r : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (e : Euclidean n) :
    fderiv ℝ reciprocal (reciprocal r) (fderiv ℝ reciprocal r e) = e := by
  have h := fderiv_comp r
    (differentiableAt_reciprocal (fun i ↦ inv_ne_zero (hr i)))
    (differentiableAt_reciprocal hr)
  have heq : reciprocal ∘ reciprocal = (id : Euclidean n → Euclidean n) := by
    funext x
    exact reciprocal_reciprocal x
  rw [heq, fderiv_id] at h
  exact (congrArg (fun f : Euclidean n →L[ℝ] Euclidean n ↦ f e) h).symm

/-- Determinants under coordinate inversion, used in
`app:ch_seed:prop:seed-frozen-menu`, Step 3. -/
theorem determinant_reciprocal {n : ℕ} {r : Euclidean n} (hr : ∀ i, r i ≠ 0) :
    cubeDeterminant (reciprocal r) = (∏ i, (r i)⁻¹)^2 * cubeDeterminant r := by
  rw [determinant_factor (fun i ↦ inv_ne_zero (hr i)), determinant_factor hr,
    reciprocal_reciprocal]
  simp only [reciprocal_apply, Finset.prod_inv_distrib]
  have hp : (∏ i, r i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hr i)
  field_simp

/-- Inversion takes characteristic tangent vectors to characteristic tangent
vectors (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem reciprocal_preserves_tangent {n : ℕ} {r e : Euclidean n}
    (hr : ∀ i, r i ≠ 0) (hchar : cubeDeterminant r = 0)
    (he : fderiv ℝ cubeDeterminant r e = 0) :
    fderiv ℝ cubeDeterminant (reciprocal r) (fderiv ℝ reciprocal r e) = 0 := by
  have hcoord (i : Fin n) : DifferentiableAt ℝ (fun x : Euclidean n ↦ x i) r :=
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap).differentiableAt
  have hg : DifferentiableAt ℝ (fun x : Euclidean n ↦ (∏ i, (x i)⁻¹)^2) r := by
    fun_prop (disch := exact hr _)
  have hev : ∀ᶠ x : Euclidean n in 𝓝 r, ∀ i, x i ≠ 0 :=
    eventually_all.mpr (fun i ↦ (hcoord i).continuousAt.eventually_ne (hr i))
  have heq : (fun x : Euclidean n ↦ cubeDeterminant (reciprocal x)) =ᶠ[𝓝 r]
      (fun x ↦ (∏ i, (x i)⁻¹)^2 * cubeDeterminant x) := by
    filter_upwards [hev] with x hx
    exact determinant_reciprocal hx
  have hp := (hg.hasFDerivAt.mul (hasFDerivAt_cubeDeterminant r)).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_cubeDeterminant (reciprocal r)).comp r
    (differentiableAt_reciprocal hr).hasFDerivAt
  have hd := congrArg (fun f : Euclidean n →L[ℝ] ℝ ↦ f e) (hc.unique hp)
  simpa [ContinuousLinearMap.comp_apply, ← (hasFDerivAt_cubeDeterminant r).fderiv,
    ← (hasFDerivAt_cubeDeterminant (reciprocal r)).fderiv, hchar, he] using hd

/-- The detecting incidence is transverse in carrier coordinates as well as
reciprocal coordinates (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem exists_transverse_carrier_tangent {n : ℕ} {k s r : Euclidean n}
    (hk : k ≠ 0) (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hchar : cubeDeterminant r = 0)
    (hdet : (∑ i, s i * quadratic (reciprocal r) i) ≠ 0) :
    ∃ e : Euclidean n, fderiv ℝ cubeDeterminant (reciprocal r) e = 0 ∧
      fderiv ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic (reciprocal x) i)
        (reciprocal r) e ≠ 0 := by
  obtain ⟨e, he, hinc⟩ := exists_transverse_tangent hk hs hr hker hchar hdet
  refine ⟨fderiv ℝ reciprocal r e, reciprocal_preserves_tangent hr hchar he, ?_⟩
  have hcoord (i : Fin n) : Differentiable ℝ (fun x : Euclidean n ↦ x i) :=
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap).differentiable
  have hf : Differentiable ℝ (fun x : Euclidean n ↦ ∑ i, k i * quadratic x i) := by
    unfold quadratic
    fun_prop
  have hc := fderiv_comp (reciprocal r) (by simpa using hf r)
    (differentiableAt_reciprocal (fun i ↦ inv_ne_zero (hr i)))
  change fderiv ℝ ((fun x : Euclidean n ↦ ∑ i, k i * quadratic x i) ∘ reciprocal)
    (reciprocal r) (fderiv ℝ reciprocal r e) ≠ 0
  rw [hc, ContinuousLinearMap.comp_apply, reciprocal_differential_comp hr,
    reciprocal_reciprocal]
  exact hinc

end JanetCartan.CubeCarrier
