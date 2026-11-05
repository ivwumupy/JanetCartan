module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputTests
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Compact coordinate derivatives for the reverse input comparison

The reverse mixed-jet comparison for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` evaluates every multilinear carrier
jet on the three coordinate directions. Basis expansion gives constant one
for the resulting pointwise norm bound. The scalar derivatives are actual
compact smooth tests, so their raw Sobolev realizations use `InputTests`.
No transverse derivative or alternative Sobolev scale is introduced.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

/-- The three literal carrier coordinate directions: one real time direction and
both directions of `Euclidean 2`. The reverse mixed-jet estimate in
`app:ch_background:eq:bg-density-adjoint` uses evaluations on this basis. -/
def inputCarrierBasis : Module.Basis (Unit ⊕ Fin 2) ℝ CarrierParameter :=
  (Module.Basis.singleton Unit ℝ).prod (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

/-- Each carrier coordinate is bounded by the original product norm. This
supplies the coefficient bound in the finite-dimensional jet comparison for
`app:ch_background:prop:bg-adjoint`. -/
theorem norm_inputCarrierBasis_repr_le (x : CarrierParameter) (i : Unit ⊕ Fin 2) :
    ‖inputCarrierBasis.repr x i‖ ≤ ‖x‖ := by
  cases i with
  | inl i =>
    simpa [inputCarrierBasis, Module.Basis.singleton_repr] using norm_fst_le x
  | inr i =>
    simp only [inputCarrierBasis, Module.Basis.prod_repr_inr,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    change ‖x.2 i‖ ≤ ‖x‖
    exact (PiLp.norm_apply_le x.2 i).trans (norm_snd_le x)

/-- Every chosen carrier direction is a unit vector in the Hilbert parameter
coordinates. Thus its Fourier derivative multiplier is controlled by the full
initial weight, with the exact `2π` normalization of
`app:ch_background:eq:bg-density-adjoint`. -/
theorem norm_toLp_inputCarrierBasis (i : Unit ⊕ Fin 2) :
    ‖WithLp.toLp 2 (inputCarrierBasis i)‖ = 1 := by
  cases i with
  | inl i => simp [inputCarrierBasis, WithLp.norm_toLp_fst]
  | inr i =>
    simp only [inputCarrierBasis, Module.Basis.prod_apply, Sum.elim_inr,
      Function.comp_apply, OrthonormalBasis.coe_toBasis, LinearMap.inr_apply,
      WithLp.norm_toLp_snd]
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one i

/-- Basis expansion bounds a carrier multilinear operator norm by the finite
sum of its coordinate evaluations, including derivative order zero. This is
the pointwise input to `lpNorm_weightedCarrierJet_le_sum_inputCoordinateTest`
for `app:ch_background:prop:bg-adjoint`. -/
theorem norm_le_sum_inputCarrierBasis {k : ℕ}
    (A : CarrierParameter [×k]→L[ℝ] ℂ) :
    ‖A‖ ≤ ∑ a : Fin k → (Unit ⊕ Fin 2), ‖A (fun j => inputCarrierBasis (a j))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun j => ∑ i, inputCarrierBasis.repr (v j) i • inputCarrierBasis i := by
    funext j
    exact (inputCarrierBasis.sum_repr (v j)).symm
  calc
    ‖A v‖ = ‖∑ a : Fin k → (Unit ⊕ Fin 2), (∏ j, inputCarrierBasis.repr (v j) (a j)) •
        A (fun j => inputCarrierBasis (a j))‖ := by
      conv_lhs => rw [hv, A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin k → (Unit ⊕ Fin 2), ‖(∏ j, inputCarrierBasis.repr (v j) (a j)) •
        A (fun j => inputCarrierBasis (a j))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin k → (Unit ⊕ Fin 2), ‖A (fun j => inputCarrierBasis (a j))‖ * ∏ j, ‖v j‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      exact norm_inputCarrierBasis_repr_le (v j) (a j)
    _ = _ := (Finset.sum_mul ..).symm

variable {n : ℕ}

/-- An actual compact smooth coordinate derivative of a carrier test. Every
inserted direction has zero transverse component: these are exclusively `z`
derivatives for `app:ch_background:eq:bg-density-adjoint`. The reverse input
comparison uses their existing raw Sobolev realizations. -/
def inputCoordinateTest (k : ℕ) (f : carrierInitialTestSpace n)
    (a : Fin k → (Unit ⊕ Fin 2)) : carrierInitialTestSpace n := by
  let ev : (CarrierVariable n [×k]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousMultilinearMap.apply ℝ _ ℂ
      (fun j => (inputCarrierBasis (a j), (0 : Euclidean (n - 1))))
  refine ⟨ev ∘ iteratedFDeriv ℝ k f.val, ?_, ?_⟩
  · exact ev.contDiff.comp (f.property.1.iteratedFDeriv_right (by simp))
  · exact (f.property.2.iteratedFDeriv (𝕜 := ℝ) k).comp_left (map_zero ev)

/-- The full derivative restricted to the chosen carrier directions equals
the derivative of the fixed-transverse slice. This identifies the compact
coordinate test used in parameter Plancherel for
`app:ch_background:prop:bg-adjoint`. -/
theorem inputCoordinateTest_eq_carrierDerivative (k : ℕ) (f : carrierInitialTestSpace n)
    (a : Fin k → (Unit ⊕ Fin 2)) (x : CarrierVariable n) :
    (inputCoordinateTest k f a).val x =
      iteratedFDeriv ℝ k (fun z => f.val (z, x.2)) x.1
        (fun j => inputCarrierBasis (a j)) := by
  let L := ContinuousLinearMap.inl ℝ CarrierParameter (Euclidean (n - 1))
  have hg : ContDiff ℝ ∞ (fun y : CarrierVariable n => f.val (y + (0, x.2))) :=
    f.property.1.comp (contDiff_id.add contDiff_const)
  have he := L.iteratedFDeriv_comp_right hg x.1 (i := k) (by simp)
  have hh : iteratedFDeriv ℝ k (fun z => f.val (z, x.2)) x.1 =
      (iteratedFDeriv ℝ k f.val x).compContinuousLinearMap (fun _ => L) := by
    simpa only [Function.comp_def, L, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, add_zero, zero_add, iteratedFDeriv_comp_add_right] using he
  rw [hh]
  rfl

/-- Evaluating the mixed jet on the carrier basis gives exactly the transverse
Bessel weight times the compact coordinate derivative. This is the scalar
input to the finite-dimensional comparison in
`app:ch_background:eq:bg-density-adjoint`. -/
theorem weightedCarrierJet_apply_inputCarrierBasis (k t : ℕ) (f : carrierInitialTestSpace n)
    (a : Fin k → (Unit ⊕ Fin 2)) (x : CarrierVariable n) :
    weightedCarrierJet k t f.val x (fun j => inputCarrierBasis (a j)) =
      etaBesselWeight t x • (inputCoordinateTest k f a).val x := by
  rw [inputCoordinateTest_eq_carrierDerivative]
  rfl

end JanetCartan.ContinuumAdjoint.DensityMultiplier
