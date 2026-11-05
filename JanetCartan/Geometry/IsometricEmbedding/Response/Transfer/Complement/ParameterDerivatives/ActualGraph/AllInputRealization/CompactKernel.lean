module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.IntegratedKernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.PDONormal

/-!
# Compact full kernels on every Euclidean L² input

The finite-coordinate bridge and compact-support Fubini needed by the low/high
source split in `app:ch_response:thm:response-literal-transfer`. The scalar
integrability theorem localizes an arbitrary L² input to compact physical
support; no smoothness or support restriction is imposed on the input.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open NormalComparison Pseudodifferential AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Literal compact matrix-kernel action on every L² input. Consumer:
`exists_compactFullEntryOperator_allInput`, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem compactFullKernelOperator_allInput_ae
    {k : Fin r → Fin r → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j)))
    (w : H) :
    compactFullKernelOperator hc hs w =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, k i j x y * w y j) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  simp only [compactFullKernelOperator, finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  refine (matrixOperator_ae_kernel _ _
    (fun i j f ↦ compactKernelOperator_ae_integral (hc i j) (hs i j) f) _ i).trans ?_
  apply Eventually.of_forall
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume w j] with y hy
  exact congrArg (k i j x y * ·) hy

/-- Fubini and finite coordinate evaluation for compact full integrands against
an arbitrary L² input. Consumer: `exists_compactFullEntryOperator_allInput`,
for `app:ch_response:thm:response-literal-transfer`. -/
theorem compactEntry_integral_sum_allInput
    (F : Fin r → Fin r → E × E → ℂ)
    (hc : ∀ i j, Continuous (F i j)) (hs : ∀ i j, HasCompactSupport (F i j))
    (w : H) (i : Fin r) :
    (∫ η, ∫ y, fun i ↦ ∑ j, F i j (η, y) * w y j) i =
      ∑ j, ∫ y, (∫ η, F i j (η, y)) * w y j := by
  have hi (i j : Fin r) : Integrable (fun p : E × E ↦ F i j p * w p.2 j)
      ((volume : Measure E).prod volume) := by
    have h := ContinuumAdjoint.DerivativeKernels.integrable_compactAmplitude_L2_weight
      ((hc i j).comp continuous_swap)
      ((hs i j).comp_homeomorph (Homeomorph.prodComm E E))
      (finiteL2CoordinateIsometry volume w j)
    apply h.swap.congr
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E))).ae_eq_comp
      (finiteL2Coordinates_apply_ae volume w j)] with p hp
    exact congrArg (F i j p * ·) hp
  have hv : Integrable (fun p : E × E ↦ fun i ↦ ∑ j, F i j p * w p.2 j)
      ((volume : Measure E).prod volume) :=
    integrable_pi_iff.mpr (fun i ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))
  rw [← integral_prod _ hv, eval_integral (fun i ↦ integrable_finsetSum _ (fun j _ ↦ hi i j)),
    integral_finsetSum _ (fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_prod_symm _ (hi i j)]
  simp only [integral_mul_const]


/-- The literal Hilbert adjoint of a compact matrix kernel on every L² input.
Consumer: `exists_compactFullEntryOperator_allInput`, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem compactFullKernelOperator_adjoint_allInput_ae
    {k : Fin r → Fin r → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j)))
    (w : H) :
    (compactFullKernelOperator hc hs).adjoint w =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (fun j ↦ ∑ i, ∫ x, star (k i j x y) * w x i) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro j
  simp only [compactFullKernelOperator, vectorMatrixL2Operator_adjoint,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  refine (matrixOperator_ae_kernel _ _
    (fun j i f ↦ compactKernelOperator_adjoint_ae_integral (hc i j) (hs i j) f) _ j).trans ?_
  apply Eventually.of_forall
  intro y
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume w i] with x hx
  exact congrArg (star (k i j x y) * ·) hx

/-- Construct a bounded compact full operator with both literal iterated
integrals on every original Euclidean vector L² input. Consumer:
`fullGraphOperator_frequencyCut_allInput`, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem exists_compactFullEntryOperator_allInput
    (F : Fin r → Fin r → (E × E) × E → ℂ)
    (hc : ∀ i j, Continuous (F i j)) (hs : ∀ i j, HasCompactSupport (F i j)) :
    ∃ T : H →L[ℂ] H,
      (∀ w : H, T w =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * w y j)) ∧
      (∀ w : H, T.adjoint w =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (∫ η, ∫ x, fun j ↦ ∑ i, star (F i j ((x, y), η)) * w x i)) := by
  have hreg i j := compactEntry_integral_regular (hc i j) (hs i j)
  let k : Fin r → Fin r → E → E → ℂ := fun i j x y ↦ ∫ η, F i j ((x, y), η)
  let T := compactFullKernelOperator (k := k) (fun i j ↦ (hreg i j).1)
    (fun i j ↦ (hreg i j).2)
  refine ⟨T, ?_, ?_⟩
  · intro w
    refine (compactFullKernelOperator_allInput_ae (fun i j ↦ (hreg i j).1)
      (fun i j ↦ (hreg i j).2) w).trans (Eventually.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    funext i
    exact (compactEntry_integral_sum_allInput (fun i j p ↦ F i j ((x, p.2), p.1))
      (fun i j ↦ (hc i j).comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst))
      (fun i j ↦ compactEntry_forward_section (hs i j) x) w i).symm
  · intro w
    refine (compactFullKernelOperator_adjoint_allInput_ae (fun i j ↦ (hreg i j).1)
      (fun i j ↦ (hreg i j).2) w).trans (Eventually.of_forall fun y ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    funext j
    have he := compactEntry_integral_sum_allInput
      (fun j i p ↦ star (F i j ((p.2, y), p.1)))
      (fun j i ↦ ((hc i j).comp ((continuous_snd.prodMk continuous_const).prodMk
        continuous_fst)).star)
      (fun j i ↦ compactEntry_reverse_section (hs i j) y) w j
    simpa only [k, Complex.star_def, integral_conj] using he.symm

end JanetCartan.FourierIntegral.FullLowBounds
