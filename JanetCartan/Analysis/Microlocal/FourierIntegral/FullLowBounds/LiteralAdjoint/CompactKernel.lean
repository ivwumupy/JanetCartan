module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Scalar
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Bridges
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Compact matrix kernels on the graph test space

The finite-coordinate bridge used by the literal full-amplitude adjoint in
`app:ch_regular_base:eq:actual-adjoint-trade`. The scalar compact-kernel theorem
supplies integrability and Fubini, with the existing Euclidean Lebesgue L² norm.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
namespace JanetCartan.FourierIntegral.FullLowBounds
open NormalComparison Pseudodifferential AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The bounded vector operator of the compact physical kernel, used to
identify the regularized full graph (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def compactFullKernelOperator
    {k : Fin r → Fin r → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j))) : H →L[ℂ] H :=
  vectorMatrixL2Operator (fun i j ↦ compactKernelOperator (μ := volume) (ν := volume)
    (hc i j) (hs i j))

/-- Literal compact-kernel action on actual smooth tests. Consumer:
`compactFullGraph_adjoint_ae`, from `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem compactFullKernelOperator_test_ae
    {k : Fin r → Fin r → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j)))
    (u : graphTestSpace n r) :
    compactFullKernelOperator hc hs (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, k i j x y * u.val y j) := by
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
  filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp u) j,
    (graphTest_memLp u).coeFn_toLp] with y hy hu
  rw [show (finiteL2CoordinateIsometry volume (graphTestToLp u)) j y = u.val y j
    from hy.trans (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v j) hu)]

/-- The actual Hilbert adjoint of the compact physical kernel on tests.
No reverse pairing is assumed (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem compactFullKernelOperator_adjoint_test_ae
    {k : Fin r → Fin r → E → E → ℂ}
    (hc : ∀ i j, Continuous (Function.uncurry (k i j)))
    (hs : ∀ i j, HasCompactSupport (Function.uncurry (k i j)))
    (u : graphTestSpace n r) :
    (compactFullKernelOperator hc hs).adjoint (graphTestToLp u) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (fun j ↦ ∑ i, ∫ x, star (k i j x y) * u.val x i) := by
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
  filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp u) i,
    (graphTest_memLp u).coeFn_toLp] with x hx hu
  rw [show (finiteL2CoordinateIsometry volume (graphTestToLp u)) i x = u.val x i
    from hx.trans (congrArg (fun v : EuclideanSpace ℂ (Fin r) ↦ v i) hu)]

end JanetCartan.FourierIntegral.FullLowBounds
