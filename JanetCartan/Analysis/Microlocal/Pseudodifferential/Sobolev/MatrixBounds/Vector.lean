module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Coordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.FiniteSums

/-!
# Matrix bounds on literal vector-valued L²

Conjugating by the proved coordinate isometry transfers the finite-sum estimate
of `app:ch_regular_base:eq:fio-input` without any norm-equivalence loss. This is
the scalar-to-vector interface for graph normal and transport constructions.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ} {I J : Type*} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

/-- The vector Sobolev membership of `app:ch_regular_base:eq:fio-input`,
expressed in the proved isometric finite coordinates. -/
def MemVectorFourierSobolev (s : ℝ) (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) : Prop :=
  MemMatrixFourierSobolev s (finiteL2CoordinateIsometry volume f)

/-- The Hilbert Sobolev norm on actual vector L² for
`app:ch_regular_base:eq:fio-input`. -/
def vectorFourierSobolevNorm (s : ℝ) (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) : ℝ :=
  matrixFourierSobolevNorm s (finiteL2CoordinateIsometry volume f)

/-- Exact order-zero normalization in `app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem vectorFourierSobolevNorm_zero
    (f : Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)) :
    vectorFourierSobolevNorm 0 f = ‖f‖ := by
  simp [vectorFourierSobolevNorm]

/-- A scalar matrix acts on literal vector-valued L² through the coordinate
isometry (`app:ch_regular_base:thm:actual-calculus`). -/
def vectorMatrixL2Operator (B : I → J → L² →L[ℂ] L²) :
    Lp (EuclideanSpace ℂ J) 2 (volume : Measure E) →L[ℂ]
      Lp (EuclideanSpace ℂ I) 2 (volume : Measure E) :=
  (finiteL2CoordinateIsometry volume).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((matrixOperator B).comp
      (finiteL2CoordinateIsometry volume).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Exact coordinate intertwining, for `app:ch_regular_base:eq:fio-input`. -/
@[simp] theorem finiteL2CoordinateIsometry_vectorMatrixL2Operator
    (B : I → J → L² →L[ℂ] L²) (f : Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)) :
    finiteL2CoordinateIsometry volume (vectorMatrixL2Operator B f) =
      matrixOperator B (finiteL2CoordinateIsometry volume f) := by
  exact (finiteL2CoordinateIsometry volume).apply_symm_apply _

/-- Reversing scalar blocks gives the literal vector Hilbert adjoint in
`app:ch_regular_base:eq:fio-input`. -/
theorem vectorMatrixL2Operator_adjoint (B : I → J → L² →L[ℂ] L²) :
    (vectorMatrixL2Operator B).adjoint = vectorMatrixL2Operator (fun j i ↦ (B i j).adjoint) := by
  unfold vectorMatrixL2Operator
  simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, matrixOperator_adjoint]
  rfl

/-- The scalar-to-vector tame interface for `app:ch_regular_base:eq:fio-input`.
For the actual PDO, `B` is the displayed scalar `twoPositionL2Operator` matrix
in `matrixTwoPositionL2Operator`; `IntegerBounds` supplies its scalar premises.
Taking `s = n`, `t = n + 1` gives the gain-one case without a new coefficient shift. -/
theorem vectorMatrixL2Operator_fourierSobolev_bound
    (B : I → J → L² →L[ℂ] L²) (s t C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hB : ∀ i j f, MemFourierSobolev s f →
      MemFourierSobolev t (B i j f) ∧
        fourierSobolevNorm t (B i j f) ≤ C * (fourierSobolevNorm s f + H * ‖f‖))
    (f : Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)) (hf : MemVectorFourierSobolev s f) :
    MemVectorFourierSobolev t (vectorMatrixL2Operator B f) ∧
      vectorFourierSobolevNorm t (vectorMatrixL2Operator B f) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
          (vectorFourierSobolevNorm s f + H * ‖f‖) := by
  simpa only [MemVectorFourierSobolev, vectorFourierSobolevNorm,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, LinearIsometryEquiv.norm_map] using
    matrixOperator_fourierSobolev_bound B s t C H hC hH hB
      (finiteL2CoordinateIsometry volume f) hf

end JanetCartan.Pseudodifferential
